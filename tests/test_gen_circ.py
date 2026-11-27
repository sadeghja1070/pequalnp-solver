#!/usr/bin/env python3
"""gen_circ on saved desk statements: which shapes it reads, and what the SAT search answers.
No Lean here (the proofs these produce were checked by hand with `lake env lean`; pnp.sh check
builds every proof again before a submit).  usage: python3 tests/test_gen_circ.py"""
import json, os, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import gen_circ  # noqa: E402

# id: (the answer's start, the gates expected or None)
EXPECT = {
    "L-meta-19069": ("exists, 8 inputs, 7 gates", None),       # an OR of ANDs, AND/OR/NOT circuit (merged #24374)
    "L-meta-19109": ("exists, 8 inputs, 8 gates", None),
    "L-meta-26275": ("exists, 8 inputs, 6 gates", None),       # graph by rows, Represents; the desk knew 7
    "L-meta-25973": ("exists, 8 inputs, 7 gates", 1),          # at most 1 NOT (notCount)
    "L-meta-25963": ("exists, 8 inputs, 7 gates", 1),
    "L-meta-26329": ("NO PROOF: UNSAT at every size up to 5", None),
    "L-meta-27139": ("NO PROOF: no circuit found", None),      # perfect matching cut: parsed, short search
}


def main():
    bad = 0
    for gid, (want, nots) in EXPECT.items():
        st = json.load(open(os.path.join(HERE, "circ", gid + ".json")))["statement"]
        assert gen_circ.parses(st), gid + " does not parse"
        t0 = time.time()
        timeout = 5 if gid == "L-meta-27139" else 120
        if gid == "L-meta-27139":
            gen_circ.CUT_LIMIT = 5
        lean, why = gen_circ.generate(gid, st, timeout)
        ok = why.startswith(want)
        if ok and nots is not None:
            ok = lean.count("⟨.not, [") <= nots
        bad += not ok
        print("%-4s %s: %s (%.0fs)" % ("ok" if ok else "FAIL", gid, why, time.time() - t0))
    print("all passed" if not bad else "%d failed" % bad)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
