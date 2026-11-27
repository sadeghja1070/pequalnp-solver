#!/usr/bin/env python3
"""Is there a resolution refutation of PHP(m, n) with at most L lines? A SAT encoding for CaDiCaL.

Lines 0..A-1 are the A axioms in a fixed order (a refutation uses every axiom of PHP: dropping any
one leaves a satisfiable formula, and axioms depend on nothing, so they can all come first). Lines
A..L-1 are resolvents of two earlier lines on some variable, no tautologies; the last line is the
empty clause. The lines are clauses (sets of literals) exactly as in Defs/ProofComplexity.lean:
R = C.erase (v, true) ∪ D.erase (v, false).

usage: resminsat.py M N L [--out cert.json] [--timeout S]
Prints SAT with the proof (and writes it as JSON lines [clause, hint]) or UNSAT."""
import argparse, glob, itertools, json, os, signal, subprocess, sys, time

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


def encode(m, n, L, premises=None, order=True, targets=None):
    """premises: the fixed first lines (default: the axioms); L counts them. targets: clauses the derived
    lines must include (a derivation of them, instead of a refutation)."""
    V = [(i, j) for i in range(m) for j in range(n)]
    lits = [(v, b) for v in V for b in (True, False)]
    li = {l: k for k, l in enumerate(lits)}
    F = premises if premises is not None else php(m, n)
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
    if targets is None:  # a refutation: the last line is the empty clause
        for k in range(len(lits)):
            e.add(-lit[L - 1][k])
    tz = []  # tz[i][t - A]: derived line t is target i
    for C in targets or []:
        s = {li[l] for l in C}
        z = [e.var() for _ in range(A, L)]
        e.add(*z)
        for t in range(A, L):
            for k in range(len(lits)):
                e.add(-z[t - A], lit[t][k] if k in s else -lit[t][k])
        tz.append(z)
    # Lines that do not depend on each other can be listed in either order. When line t does not use
    # line t-1, ask line t-1 to come first in a fixed order of clauses (lexicographic on the literal
    # bits): any refutation can be brought to this form by swapping such neighbours (each swap removes
    # one inversion, and swaps keep every premise before its use). The last line (the empty clause)
    # stays where it is.
    if order:
        K = len(lits)
        for t in range(A + 1, L - 1 if targets is None else L):
            x, y = lit[t - 1], lit[t]
            s = [e.var() for _ in range(K)]
            q = [None] + [e.var() for _ in range(1, K)]  # q[k]: x and y agree on bits 0..k-1
            e.add(hint[t][0][t - 1], hint[t][1][t - 1], *s)
            for k in range(K):
                e.add(-s[k], -x[k]); e.add(-s[k], y[k])
                if k:
                    e.add(-s[k], q[k])
                    e.add(-q[k], -x[k - 1], y[k - 1]); e.add(-q[k], x[k - 1], -y[k - 1])
                    if k > 1:
                        e.add(-q[k], q[k - 1])
    # every derived line but the last is a premise of a later line (a shortest refutation has no dead line)
    # (with targets: every derived line is a target or a premise of a later line)
    for t in range(A, L - 1 if targets is None else L):
        e.add(*[x for u in range(t + 1, L) for x in (hint[u][0][t], hint[u][1][t])], *[z[t - A] for z in tz])
    # pigeons and holes can be renamed (the axioms are put back in their order): the last pivot is (0, 0).
    # Only with the axioms alone as premises: other premises tell pigeons apart, and the cut would be unsound.
    if targets is not None:
        pass  # no last pivot to fix
    elif premises is None:
        e.add(hint[L - 1][2][V.index((0, 0))])
    else:  # holes are still all alike when every premise set is closed under renaming holes: last pivot in hole 0
        e.add(*[hint[L - 1][2][k] for k, v in enumerate(V) if v[1] == 0])
    return e, lit, hint, lits, V, F


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("m", type=int); ap.add_argument("n", type=int); ap.add_argument("L", type=int)
    ap.add_argument("--out"); ap.add_argument("--timeout", type=int, default=3600)
    ap.add_argument("--no-order", action="store_true", help="drop the line-order symmetry cut")
    ap.add_argument("--premises", help="JSON list of clauses to take as the first lines (instead of the axioms); "
                                       "L is then the number of premises plus resolvents")
    ap.add_argument("--targets", help="JSON list of clauses to derive (instead of the empty clause)")
    a = ap.parse_args()
    prem = None
    if a.premises:
        prem = [sorted((tuple(v), b) for v, b in C) for C in json.load(open(a.premises))]
    tg = [sorted((tuple(v), b) for v, b in C) for C in json.load(open(a.targets))] if a.targets else None
    e, lit, hint, lits, V, F = encode(a.m, a.n, a.L, prem, not a.no_order, tg)
    path = os.path.join(HERE, "res_%d_%d_%d_%d.cnf" % (a.m, a.n, a.L, os.getpid()))
    with open(path, "w") as f:
        f.write("p cnf %d %d\n" % (e.n, len(e.cls)))
        for c in e.cls:
            f.write(" ".join(map(str, c)) + " 0\n")
    cad = sorted(glob.glob(os.path.expanduser("~/.elan/toolchains/*/bin/cadical")))[-1]
    t0 = time.time()
    # the solver must not outlive this script: a kill here (SIGTERM, SIGINT) stops it and removes the file
    signal.signal(signal.SIGTERM, lambda *_: sys.exit(143))
    proc = subprocess.Popen([cad, "-q", "-t", str(a.timeout), path], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    try:
        out, _ = proc.communicate()
    finally:
        if proc.poll() is None:
            proc.kill(); proc.wait()
        os.remove(path)
    r = subprocess.CompletedProcess(proc.args, proc.returncode, out, "")
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
