#!/usr/bin/env python3
"""Put a refutation together from pieces, matching lines by their clauses.

Each piece is a list of lines in gen_pcx's format (oldest first, [clause, hint], hints index the
piece's own lines). Lines are taken piece by piece; a clause already present is not repeated, and a
hint is rewritten to point at the lines holding the same clauses. Lines no later line uses (but the
empty clause) are then dropped, and the result is checked as a refutation of PHP(m, n).

usage: splice.py M N --part scheme:A:B --part FILE:START ... [--out best_M_N.json]
  The usual use: the scheme's axioms and first level, a searched middle, the scheme's last level:
    splice.py 4 3 --part scheme:0:28 --part tw_15.json:25 --part scheme:46: --out best_4_3.json"""
import argparse, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gen_pcx


def merge(pieces):
    """pieces: (lines, start): take lines[start:] of each, in order. Premises are looked up by clause."""
    out, at = [], {}
    for lines, start in pieces:
        for C, h in lines[start:]:
            if C in at:
                continue
            if h is None:
                hint = None
            else:
                P, N = lines[h[0]][0], lines[h[1]][0]
                assert P in at and N in at, "a premise of %s is in no earlier piece" % sorted(C)
                hint = (at[P], at[N], h[2])
            at[C] = len(out)
            out.append((C, hint))
    return out


def prune(lines):
    """Drop derived lines nothing uses (keep axioms and the first empty clause); renumber hints."""
    end = next(t for t, (C, _) in enumerate(lines) if not C)
    keep = set(range(end + 1))
    need = {end}
    for t in range(end, -1, -1):
        if t in need and lines[t][1] is not None:
            need |= {lines[t][1][0], lines[t][1][1]}
    keep = sorted(t for t in keep if t in need or lines[t][1] is None)
    new = {t: i for i, t in enumerate(keep)}
    return [(lines[t][0], None if lines[t][1] is None else (new[lines[t][1][0]], new[lines[t][1][1]], lines[t][1][2]))
            for t in keep]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("m", type=int); ap.add_argument("n", type=int)
    ap.add_argument("--part", action="append", required=True,
                    help="scheme:A:B (the scheme's lines A..B-1) or FILE:START (a search result from line START)")
    ap.add_argument("--out")
    a = ap.parse_args()
    scheme = gen_pcx.scheme(a.m, a.n)
    pieces = []
    for p in a.part:
        if p.startswith("scheme:"):
            _, x, y = p.split(":")
            lines = scheme[:int(y)] if y else scheme
            pieces.append((lines, int(x)))
        else:
            f, s = p.rsplit(":", 1)
            pieces.append((gen_pcx.load(f), int(s)))
    lines = prune(merge(pieces))
    n = gen_pcx.check(a.m, a.n, lines)
    print("refutation of PHP(%d,%d): %d lines, checked" % (a.m, a.n, n))
    if a.out:
        gen_pcx.save(lines, a.out)
        print("wrote", a.out)


if __name__ == "__main__":
    main()
