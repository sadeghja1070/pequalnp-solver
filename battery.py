#!/usr/bin/env python3
"""Try a battery of standard Lean tactics on any statement, all in one Lean run.

Each tactic gets its own copy of the theorem (its own heartbeat budget, and an error in one copy
does not stop the others), so one `lake env lean` run tries them all. The first copy that checks
gives the proof: the step's theorem with that tactic alone. Nothing here can make a wrong claim:
the file it returns has passed Lean, and pnp.sh check builds it again before anything is sent.

usage: battery.py --json <lease json> [--out FILE] [--timeout 300]
       battery.py --id L-gct-126 --statement-file st.txt [--import PEqualNP.Defs ...]
Prints PROOF: ... on success (exit 0), NO PROOF: ... otherwise (exit 1)."""
import argparse, json, os, re, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "pequalnp-proofs"))
WORK = os.path.join(HERE, "out", "battery")

# Cheap, general closers. No native_decide (refused by the checker), nothing that needs the network.
TACTICS = [
    "decide",
    "intros\n  ring",
    "intros\n  norm_num",
    "intros\n  simp",
    "intros\n  omega",
    "intros\n  linarith",
    "intros\n  nlinarith",
    "intros\n  positivity",
    "intros\n  simp\n  ring",
    "intros\n  norm_num\n  ring_nf",
    "tauto",
    "aesop",
    "decide +kernel",
]
HEARTBEATS = 400000


def header(imports):
    """Mathlib, then the step's own imports (the desk lists them; PEqualNP.Defs when not known)."""
    mods = ["Mathlib"] + [m for m in (imports or ["PEqualNP.Defs"]) if m != "Mathlib"]
    return "".join("import %s\n" % m for m in mods) + "\n"


def theorem(name, st, tac):
    body = "\n".join("  " + l.strip() for l in tac.split("\n"))
    return "set_option maxHeartbeats %d in\ntheorem %s : %s := by\n%s\n" % (HEARTBEATS, name, st, body)


def prove(gid, st, imports=None, timeout=300):
    """(lean, why): the step's file with the first tactic that checks, or (None, why)."""
    os.makedirs(WORK, exist_ok=True)
    mod = gid.replace("-", "_")
    head = header(imports)
    text, spans, line = head, [], head.count("\n") + 1
    for i, tac in enumerate(TACTICS):
        block = theorem("PEqualNP.Outside.%s_battery_%d" % (mod, i), st, tac) + "\n"
        spans.append((line, line + block.count("\n") - 1))
        text += block
        line += block.count("\n")
    path = os.path.join(WORK, mod + "_battery.lean")
    open(path, "w", encoding="utf-8").write(text)
    t0 = time.time()
    try:
        r = subprocess.run(["lake", "env", "lean", path], cwd=os.path.join(REPO, "lean"), capture_output=True,
                           text=True, timeout=timeout)
        out = r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        return None, "NO PROOF: the battery ran past %ds" % timeout
    bad = set()
    for m in re.finditer(r":(\d+):\d+: error", out):
        ln = int(m.group(1))
        for i, (a, b) in enumerate(spans):
            if a <= ln <= b:
                bad.add(i)
        if not any(a <= ln <= b for a, b in spans):  # an error outside every copy: the statement or imports
            return None, "NO PROOF: does not elaborate here: %s" % out.strip().splitlines()[0][:200]
    for i, tac in enumerate(TACTICS):
        if i not in bad:
            lean = head + theorem("PEqualNP.Outside.%s" % mod, st, tac)
            return lean, "battery: %s (%.0fs)" % (tac.replace("\n  ", "; "), time.time() - t0)
    return None, "NO PROOF: none of %d tactics closes it (%.0fs)" % (len(TACTICS), time.time() - t0)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--json")
    ap.add_argument("--id")
    ap.add_argument("--statement-file")
    ap.add_argument("--import", dest="imports", action="append")
    ap.add_argument("--out")
    ap.add_argument("--timeout", type=float, default=300)
    a = ap.parse_args()
    if a.json:
        g = json.load(open(a.json))["gap"]
        gid, st, imports = g["id"], g["statement"], g.get("imports") or []
        out = a.out or os.path.join(REPO, g["file"])
    else:
        gid, st, imports = a.id, open(a.statement_file, encoding="utf-8").read().strip(), a.imports or []
        out = a.out or os.path.join(HERE, "out", gid.replace("-", "_") + ".lean")
    lean, why = prove(gid, st, imports, a.timeout)
    if lean is None:
        print(why); sys.exit(1)
    open(out, "w", encoding="utf-8").write(lean)
    print("PROOF: %s %s -> %s" % (gid, why, out))


if __name__ == "__main__":
    main()
