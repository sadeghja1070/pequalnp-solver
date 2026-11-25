#!/usr/bin/env python3
"""Race for the true twin of a 'False:' direction-3 step the desk handed us.

usage: race.py L-meta-N [--submit]
  L-meta-N must be leased by us (its .pnp/L-meta-N.json exists) and be the 'False:' claim for a
  monotone six-input table.  Its true twin is L-meta-(N-1).  The script:
    1. reads the table, asks the desk for the twin's state (one GET);
    2. builds and Lean-checks a proof of the twin under a scratch module (nothing sent);
    3. hands L-meta-N back as statement_seems_false (the twin's proof shows it false);
    4. leases the twin with `next --proof-of`, regenerates the file from the official statement,
       runs `pnp.sh check`;
    5. only with --submit: `pnp.sh submit` (opens the pull request).
It stops early when the twin is already proved or has a pull request waiting."""
import json, os, re, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "pequalnp-proofs"))


def pnp(*args):
    r = subprocess.run([os.path.join(REPO, "tools", "pnp.sh"), *args], cwd=REPO, capture_output=True, text=True)
    out = (r.stdout + r.stderr).strip()
    print("  pnp.sh %s -> %s" % (" ".join(args), out.splitlines()[-1] if out else r.returncode))
    return r.returncode, out


def state(gap):
    # curl, like pnp.sh: the desk refuses Python's default client
    r = subprocess.run(["curl", "--proto", "=https", "-fsS", "-m", "10", "-G", "https://pequalnp.com/desk/step",
                        "--data-urlencode", "gap=" + gap], capture_output=True, text=True)
    time.sleep(2)
    if r.returncode != 0:
        return "unknown", None
    d = json.loads(r.stdout)
    return d.get("state"), d.get("prs")


def main():
    neg, submit = sys.argv[1], "--submit" in sys.argv
    m = re.fullmatch(r"L-meta-(\d+)", neg)
    if not m:
        sys.exit("give a step id like L-meta-13686")
    pos = "L-meta-%d" % (int(m.group(1)) - 1)
    g = json.load(open(os.path.join(REPO, ".pnp", neg + ".json")))["gap"]
    t = re.search(r"Nat\.testBit \((\d+) \* 2 \^ 32 \+ (\d+)\)", g["statement"])
    if not (g["statement"].startswith("¬ (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6") and t):
        sys.exit("%s is not a 'False:' direction-3 step" % neg)
    hi, lo = t.group(1), t.group(2)
    # Already ours (submitted, or held): the desk may not show our pull request yet, so look locally.
    mine = (subprocess.run(["git", "rev-parse", "--verify", "-q", "refs/heads/" + pos], cwd=REPO,
                           capture_output=True).returncode == 0
            or any(os.path.exists(os.path.join(REPO, ".pnp", pos + ext)) for ext in (".json", ".done")))
    if mine:
        print("STOP: %s is already ours (submitted or held); nothing to race for." % pos)
        return 3
    st, prs = state(pos)
    print("twin %s: %s %s" % (pos, st, prs or ""))
    if st not in ("open", "leased"):
        print("STOP: the twin is %s; nothing to race for. Hand %s back with: tools/pnp.sh release %s statement_seems_false"
              % (st, neg, neg))
        return 2
    # 2. local proof under a scratch module
    # a race is only worth it when fast: the true twin's holder is working on it too
    scratch = subprocess.run([os.path.join(HERE, "test_build.sh"), hi, lo, "R" + m.group(1)], capture_output=True, text=True,
                             env=dict(os.environ, GEN_TIMEOUT="240"))
    print(scratch.stdout.strip())
    if "LEAN OK" not in scratch.stdout:
        print("STOP: no checked proof; %s stays held. Release it when done looking." % neg)
        return 1
    # 3. the claim we hold is false: hand it back
    pnp("release", neg, "statement_seems_false")
    sk = os.path.join(REPO, g["file"])
    if os.path.exists(sk):
        os.remove(sk)
    os.rename(os.path.join(REPO, ".pnp", neg + ".json"), os.path.join(REPO, ".pnp", neg + ".done"))
    # 4. lease the twin with a proof in hand; regenerate from the official statement; check
    code, out = pnp("next", "--proof-of", pos)
    if code != 0 or not os.path.exists(os.path.join(REPO, ".pnp", pos + ".json")):
        print(out)
        print("STOP: the desk did not lease %s" % pos)
        return 1
    sys.path.insert(0, HERE)
    from gen_dir3 import STMT
    official = json.load(open(os.path.join(REPO, ".pnp", pos + ".json")))["gap"]
    built = os.path.join(HERE, "out", "L_meta_scratch_R%s.lean" % m.group(1))
    if official["statement"] == STMT.format(hi=hi, lo=lo) and os.path.exists(built):
        # the proof already built under the scratch name, renamed: no second witness search
        text = open(built, encoding="utf-8").read().replace("L_meta_scratch_R%s" % m.group(1), official["module"].split(".")[-1])
        open(os.path.join(REPO, official["file"]), "w", encoding="utf-8").write(text)
        print("reused the checked scratch proof for %s" % pos)
    else:
        gen = subprocess.run([sys.executable, "-I", os.path.join(HERE, "gen_dir3.py"), "--json",
                              os.path.join(REPO, ".pnp", pos + ".json")], capture_output=True, text=True)
        print(gen.stdout.strip() or gen.stderr.strip())
        if not gen.stdout.startswith("PROOF"):
            print("STOP: could not generate from the official statement; release %s if it stays that way" % pos)
            return 1
    code, out = pnp("check", pos)
    if code != 0:
        print(out[-3000:])
        print("STOP: check failed for %s" % pos)
        return 1
    if not submit:
        print("READY: %s is checked and leased. Submit with: tools/pnp.sh submit %s" % (pos, pos))
        return 0
    code, out = pnp("submit", pos)
    print(out[-2000:])
    return code


if __name__ == "__main__":
    sys.exit(main())
