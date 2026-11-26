#!/usr/bin/env python3
"""Lean files for 'some refutation of the pigeonhole formula has at most L lines' steps.

A refutation is a list of resolution lines, OLDEST FIRST, each [clause, hint]: a clause is a list
of literals [[i, j], b] (variable (i, j): pigeon i sits in hole j; b the sign), a hint is null for
an axiom or [p, q, [i, j]] for the resolvent of lines p (holding the variable positively) and q
(holding it negatively). The same list serves two systems:
  - resolution (IsRefutation): the certificate of chkR, as in the merged L_pcx_171;
  - Res(⊕) (IsLinRefutation): every clause read as a linear clause (linOfClause), every resolution
    step a Res(⊕) step on the one-variable form {v}, the certificate of chkL.
The checker, its soundness proofs and the axiom recognisers are copied from L_pcx_171 (merged).

usage: gen_pcx.py --proof P.json --system res|lin --m 4 --n 3 --bound 55 --module L_pcx_121 [--out F]
       gen_pcx.py --scheme --m 4 --n 3 --save P.json     the pigeon-by-pigeon refutation (58 lines for 4, 3)"""
import argparse, json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", "pequalnp-proofs"))
PRELUDE_FROM = os.path.join(REPO, "lean", "PEqualNP", "Outside", "L_pcx_171.lean")


# ---- refutations ----

def php(m, n):
    F = [frozenset(((i, j), True) for j in range(n)) for i in range(m)]
    F += [frozenset({((i, j), False), ((k, j), False)}) for j in range(n) for i in range(m) for k in range(i + 1, m)]
    return F


def check(m, n, lines):
    """Raise unless `lines` is a resolution refutation of PHP(m, n) (the rules of Defs/ProofComplexity)."""
    F = set(php(m, n))
    seen = []
    for t, (C, h) in enumerate(lines):
        if h is None:
            assert C in F, "line %d: not an axiom" % t
        else:
            p, q, v = h
            assert p < t and q < t, "line %d: premises must come before" % t
            P, N = seen[p], seen[q]
            assert (v, True) in P and (v, False) in N, "line %d: pivot not in its premises" % t
            assert C == (P - {(v, True)}) | (N - {(v, False)}), "line %d: not the resolvent" % t
        seen.append(C)
    assert frozenset() in seen, "no empty clause"
    return len(lines)


def scheme(m, n):
    """The pigeon-by-pigeon refutation: D(k, S) = 'some pigeon of the first k sits outside S'
    (|S| = k - 1), from D(k, S) and the hole clauses for pigeon k+1, then pigeon k+1's clause."""
    assert m == n + 1
    lines, index = [], {}

    def add(C, h):
        C = frozenset(C)
        if C in index:
            return index[C]
        index[C] = len(lines); lines.append((C, h))
        return index[C]

    for C in php(m, n):  # every axiom is used
        add(C, None)
    x = lambda i, j: (i, j)
    D = {frozenset(): index[php(m, n)[0]]}  # D(1, ∅) is pigeon 0's clause
    for k in range(1, m):  # pigeons 0..k-1 done; add pigeon k
        newD = {}
        for S in D:
            pass
        holes = range(n)
        from itertools import combinations
        for Sp in combinations(holes, k):
            Sp = frozenset(Sp)
            cur = index[php(m, n)[k]]  # pigeon k's clause
            for h in sorted(Sp):
                S = Sp - {h}
                e = D[S]
                for i in range(k):  # remove x(i, h) with the hole clause (i, k, h)
                    C = lines[e][0]
                    R = (C - {(x(i, h), True)}) | {(x(k, h), False)}
                    hc = index[frozenset({(x(i, h), False), (x(k, h), False)})]
                    e = add(R, (e, hc, x(i, h)))
                C = lines[cur][0]
                R = (C - {(x(k, h), True)}) | (lines[e][0] - {(x(k, h), False)})
                cur = add(R, (cur, e, x(k, h)))
            newD[Sp] = cur
        D = newD
    return [(C, h) for C, h in lines]


def load(path):
    out = []
    for C, h in json.load(open(path)):
        C = frozenset((tuple(v), b) for v, b in C)
        out.append((C, None if h is None else (h[0], h[1], tuple(h[2]))))
    return out


def save(lines, path):
    json.dump([[[[list(v), b] for v, b in sorted(C)], None if h is None else [h[0], h[1], list(h[2])]] for C, h in lines],
              open(path, "w"))


# ---- Lean ----

def lit(v, b):
    return "((%d, %d), %s)" % (v[0], v[1], "true" if b else "false")


def clause(C):
    return "∅" if not C else "{%s}" % ", ".join(lit(v, b) for v, b in sorted(C))


def linclause(C):
    return "∅" if not C else "{%s}" % ", ".join("(({(%d, %d)} : Finset (Fin %%(m)d × Fin %%(n)d)), %s)" % (v[0], v[1], "true" if b else "false")
                                                for v, b in sorted(C))


def prelude(ns):
    """The helper section of L_pcx_171 up to its certificate, in our own namespace."""
    t = open(PRELUDE_FROM, encoding="utf-8").read()
    i = t.index("namespace PEqualNP.Outside.L_pcx_171_aux")
    j = t.index("def cert")
    body = t[i:j].replace("L_pcx_171_aux", ns)
    return "import Mathlib\nimport PEqualNP.Defs\n\n" + body


def lean(lines, system, m, n, bound, module):
    ns = module + "_aux"
    L = len(lines)
    rows = []
    for t in range(L - 1, -1, -1):  # newest first; a premise at p is entry t-1-p of the tail
        C, h = lines[t]
        if system == "res":
            hint = "none" if h is None else "some (%d, %d, (%d, %d))" % (t - 1 - h[0], t - 1 - h[1], h[2][0], h[2][1])
            rows.append("  (%s, %s)" % (clause(C), hint))
        else:
            R = linclause(C) % {"m": m, "n": n}
            if h is None:
                st = ".ax %s" % clause(C)
            else:  # chkL: entry i holds f = 0 (the negative literal), entry j holds f = 1
                st = ".rs %d %d {(%d, %d)}" % (t - 1 - h[1], t - 1 - h[0], h[2][0], h[2][1])
            rows.append("  (%s, %s)" % (R, st))
    V = "Fin %d × Fin %d" % (m, n)
    if system == "res":
        ty = "List (Clause (%s) × Option (ℕ × ℕ × (%s)))" % (V, V)
        chk = "chkR (axPHP %d %d) cert = true" % (m, n)
        empty = "(∅ : Clause (%s)) ∈ cert.map Prod.fst" % V
        stmt = ("∃ π : List (PEqualNP.ProofComplexity.Clause (%s)), PEqualNP.ProofComplexity.IsRefutation "
                "(PEqualNP.ProofComplexity.PHP %d %d) π ∧ π.length ≤ %d") % (V, m, n, bound)
        sound = "chkR_sound"
    else:
        ty = "List (LinClause (%s) × Step (%s))" % (V, V)
        chk = "chkL (axPHP %d %d) cert = true" % (m, n)
        empty = "(∅ : LinClause (%s)) ∈ cert.map Prod.fst" % V
        stmt = ("∃ π : List (PEqualNP.ProofComplexity.LinClause (%s)), PEqualNP.ProofComplexity.IsLinRefutation "
                "(PEqualNP.ProofComplexity.PHP %d %d) π ∧ π.length ≤ %d") % (V, m, n, bound)
        sound = "chkL_sound"
    q = "PEqualNP.Outside.%s." % ns
    return (prelude(ns)
            + "def cert : %s := [\n%s]\n\n" % (ty, ",\n".join(rows))
            + "set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\ntheorem hc : %s := by decide +kernel\n\n" % chk
            + "set_option maxRecDepth 100000 in\ntheorem hm : %s := by decide +kernel\n\n" % empty
            + "set_option maxRecDepth 100000 in\ntheorem hl : (cert.map Prod.fst).length ≤ %d := by decide +kernel\n\n" % bound
            + "end PEqualNP.Outside.%s\n\n" % ns
            + "theorem PEqualNP.Outside.%s : %s := by\n" % (module, stmt)
            + "  exact ⟨%scert.map Prod.fst, ⟨%s%s _ (%saxPHP %d %d) (%saxPHP_sound %d %d) _ %shc, %shm⟩, %shl⟩\n"
            % (q, q, sound, q, m, n, q, m, n, q, q, q))


STMT = {"res": r"∃ π : List \(PEqualNP\.ProofComplexity\.Clause \(Fin (\d+) × Fin (\d+)\)\), PEqualNP\.ProofComplexity\.IsRefutation "
               r"\(PEqualNP\.ProofComplexity\.PHP \1 \2\) π ∧ π\.length ≤ (\d+)",
        "lin": r"∃ π : List \(PEqualNP\.ProofComplexity\.LinClause \(Fin (\d+) × Fin (\d+)\)\), PEqualNP\.ProofComplexity\.IsLinRefutation "
               r"\(PEqualNP\.ProofComplexity\.PHP \1 \2\) π ∧ π\.length ≤ (\d+)"}


def read_statement(st):
    """(system, m, n, bound) for a step this generator proves, else None."""
    st = re.sub(r"\s+", " ", st).strip()
    for system, pat in STMT.items():
        mm = re.fullmatch(pat, st)
        if mm:
            return system, int(mm.group(1)), int(mm.group(2)), int(mm.group(3))
    return None


def best(m, n):
    """The shortest refutation of PHP(m, n) known here: a saved one (pcx/best_M_N.json) or the scheme."""
    path = os.path.join(HERE, "best_%d_%d.json" % (m, n))
    cands = [scheme(m, n)] if m == n + 1 else []
    if os.path.exists(path):
        cands.append(load(path))
    good = [c for c in cands if check(m, n, c)]
    return min(good, key=len) if good else None


def generate(gid, st):
    """(lean, why) for a pcx refutation-length step, or (None, why)."""
    r = read_statement(st)
    if r is None:
        return None, "SKIP: not a refutation-length step"
    system, m, n, bound = r
    lines = best(m, n)
    if lines is None or len(lines) > bound:
        return None, "NO PROOF: the shortest refutation of PHP(%d,%d) known here has %s lines, the step asks %d" % (
            m, n, len(lines) if lines else "no", bound)
    return lean(lines, system, m, n, bound, gid.replace("-", "_")), "pcx %s, PHP(%d,%d), %d lines (bound %d)" % (system, m, n, len(lines), bound)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", help="a lease: prove its step with the shortest refutation known here")
    ap.add_argument("--timeout", type=float, default=0, help="ignored (no search runs here)")
    ap.add_argument("--proof"); ap.add_argument("--scheme", action="store_true"); ap.add_argument("--save")
    ap.add_argument("--system", choices=("res", "lin")); ap.add_argument("--m", type=int); ap.add_argument("--n", type=int)
    ap.add_argument("--bound", type=int); ap.add_argument("--module"); ap.add_argument("--out")
    a = ap.parse_args()
    if a.json:
        g = json.load(open(a.json))["gap"]
        text, why = generate(g["id"], g["statement"])
        if text is None:
            print(why); sys.exit(1)
        out = a.out or os.path.join(REPO, g["file"])
        open(out, "w", encoding="utf-8").write(text)
        print("PROOF: %s %s -> %s" % (g["id"], why, out)); return
    lines = scheme(a.m, a.n) if a.scheme else load(a.proof)
    print("refutation of PHP(%d,%d): %d lines, checked" % (a.m, a.n, check(a.m, a.n, lines)))
    if a.save:
        save(lines, a.save)
    if a.system:
        text = lean(lines, a.system, a.m, a.n, a.bound or len(lines), a.module)
        open(a.out, "w", encoding="utf-8").write(text)
        print("wrote", a.out)


if __name__ == "__main__":
    main()
