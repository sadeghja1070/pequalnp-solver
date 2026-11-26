#!/usr/bin/env python3
"""Is there a resolution refutation of PHP(m, n) with at most L lines? A SAT encoding for CaDiCaL.

Lines 0..A-1 are the A axioms in a fixed order (a refutation uses every axiom of PHP: dropping any
one leaves a satisfiable formula, and axioms depend on nothing, so they can all come first). Lines
A..L-1 are resolvents of two earlier lines on some variable, no tautologies; the last line is the
empty clause. The lines are clauses (sets of literals) exactly as in Defs/ProofComplexity.lean:
R = C.erase (v, true) ∪ D.erase (v, false).

usage: resminsat.py M N L [--out cert.json] [--timeout S]
Prints SAT with the proof (and writes it as JSON lines [clause, hint]) or UNSAT."""
import argparse, glob, itertools, json, os, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))


def php(m, n):
    F = [sorted(((i, j), True) for j in range(n)) for i in range(m)]
    F += [[((i, j), False), ((k, j), False)] for j in range(n) for i in range(m) for k in range(i + 1, m)]
    return F


class Enc:
    def __init__(self):
        self.n, self.cls = 0, []

    def var(self):
        self.n += 1
        return self.n

    def add(self, *c):
        self.cls.append(c)

    def exactly_one(self, xs):
        self.add(*xs)
        # sequential at-most-one
        if len(xs) > 1:
            s = [self.var() for _ in xs[:-1]]
            self.add(-xs[0], s[0])
            for i in range(1, len(xs) - 1):
                self.add(-xs[i], s[i]); self.add(-s[i - 1], s[i]); self.add(-xs[i], -s[i - 1])
            self.add(-xs[-1], -s[-1])


def encode(m, n, L):
    V = [(i, j) for i in range(m) for j in range(n)]
    lits = [(v, b) for v in V for b in (True, False)]
    li = {l: k for k, l in enumerate(lits)}
    F = php(m, n)
    A = len(F)
    e = Enc()
    lit = [[e.var() for _ in lits] for _ in range(L)]
    for t, C in enumerate(F):  # axioms first, fixed
        s = {li[l] for l in C}
        for k in range(len(lits)):
            e.add(lit[t][k] if k in s else -lit[t][k])
    for t in range(L):  # no tautologies
        for v in V:
            e.add(-lit[t][li[(v, True)]], -lit[t][li[(v, False)]])
    hint = {}
    for t in range(A, L):
        p1 = [e.var() for _ in range(t)]
        p2 = [e.var() for _ in range(t)]
        pv = [e.var() for _ in V]
        e.exactly_one(p1); e.exactly_one(p2); e.exactly_one(pv)
        a = [e.var() for _ in lits]  # a[k]: the first premise holds literal k
        b = [e.var() for _ in lits]
        for p in range(t):
            for k in range(len(lits)):
                e.add(-p1[p], -lit[p][k], a[k]); e.add(-p1[p], lit[p][k], -a[k])
                e.add(-p2[p], -lit[p][k], b[k]); e.add(-p2[p], lit[p][k], -b[k])
        for vi, v in enumerate(V):
            kp, kn = li[(v, True)], li[(v, False)]
            e.add(-pv[vi], a[kp]); e.add(-pv[vi], b[kn])
            e.add(-pv[vi], -lit[t][kp]); e.add(-pv[vi], -lit[t][kn])
            for k in (kp, kn):  # not the pivot: R[k] = a[k] or b[k]
                e.add(pv[vi], -lit[t][k], a[k], b[k]); e.add(pv[vi], -a[k], lit[t][k]); e.add(pv[vi], -b[k], lit[t][k])
        # a resolvent is new: it differs from every earlier line (a shortest proof repeats nothing)
        for p in range(t):
            d = [e.var() for _ in lits]
            e.add(*d)
            for k in range(len(lits)):
                e.add(-d[k], lit[t][k], lit[p][k]); e.add(-d[k], -lit[t][k], -lit[p][k])
        # resolvents in order of their second premise, a cheap symmetry cut: none
        hint[t] = (p1, p2, pv)
    for k in range(len(lits)):
        e.add(-lit[L - 1][k])
    # every derived line but the last is a premise of a later line (a shortest refutation has no dead line)
    for t in range(A, L - 1):
        e.add(*[x for u in range(t + 1, L) for x in (hint[u][0][t], hint[u][1][t])])
    # pigeons and holes can be renamed (the axioms are put back in their order): the last pivot is (0, 0)
    e.add(hint[L - 1][2][V.index((0, 0))])
    return e, lit, hint, lits, V, F


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("m", type=int); ap.add_argument("n", type=int); ap.add_argument("L", type=int)
    ap.add_argument("--out"); ap.add_argument("--timeout", type=int, default=3600)
    a = ap.parse_args()
    e, lit, hint, lits, V, F = encode(a.m, a.n, a.L)
    path = os.path.join(HERE, "res_%d_%d_%d_%d.cnf" % (a.m, a.n, a.L, os.getpid()))
    with open(path, "w") as f:
        f.write("p cnf %d %d\n" % (e.n, len(e.cls)))
        for c in e.cls:
            f.write(" ".join(map(str, c)) + " 0\n")
    cad = sorted(glob.glob(os.path.expanduser("~/.elan/toolchains/*/bin/cadical")))[-1]
    t0 = time.time()
    r = subprocess.run([cad, "-q", "-t", str(a.timeout), path], capture_output=True, text=True)
    os.remove(path)
    dt = time.time() - t0
    if r.returncode == 20:
        print("UNSAT: no resolution refutation of PHP(%d,%d) with %d lines (%.0fs, %d vars, %d clauses)"
              % (a.m, a.n, a.L, dt, e.n, len(e.cls))); return
    if r.returncode != 10:
        print("UNKNOWN after %.0fs (exit %d)" % (dt, r.returncode)); return
    true = {int(x) for l in r.stdout.splitlines() if l.startswith("v") for x in l.split()[1:] if int(x) > 0}
    lines = []
    for t in range(a.L):
        C = [lits[k] for k in range(len(lits)) if lit[t][k] in true]
        if t < len(F):
            lines.append((C, None))
        else:
            p1, p2, pv = hint[t]
            i = next(p for p in range(t) if p1[p] in true)
            j = next(p for p in range(t) if p2[p] in true)
            v = next(V[k] for k in range(len(V)) if pv[k] in true)
            lines.append((C, (i, j, v)))
    print("SAT: a refutation of PHP(%d,%d) with %d lines (%.0fs)" % (a.m, a.n, a.L, dt))
    if a.out:
        json.dump([[[[list(l[0]), l[1]] for l in C], h] for C, h in lines], open(a.out, "w"))


if __name__ == "__main__":
    main()
