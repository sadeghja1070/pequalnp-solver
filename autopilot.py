#!/usr/bin/env python3
"""Ask the desk for solid prove steps until one is a direction-3 claim we can prove, then prove it.

usage: autopilot.py [--interval 45] [--max-hours 3] [--submit]
  Each round: `pnp.sh next --level solid --kind prove` (one lease at a time).
  - a direction-3 positive claim: generate the proof from the lease (gen_dir3.py --json), renew the
    lease, `pnp.sh check`. Without --submit it stops there with the step checked and held; with
    --submit it runs `pnp.sh submit` and goes on.
  - anything else (the 'False:' twins, other families): handed back as `other`, which also keeps the
    desk from offering it to us again for an hour.
  The desk asks for one request every few seconds at most; rounds are --interval seconds apart.
Log lines go to stdout; a READY line names a checked step waiting for its pull request."""
import argparse, json, os, re, subprocess, sys, threading, time

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "pequalnp-proofs"))
sys.path.insert(0, HERE)
from gen_dir3 import STMT  # noqa: E402


def log(msg):
    print(time.strftime("%H:%M:%S"), msg, flush=True)


def pnp(*args, timeout=None):
    r = subprocess.run([os.path.join(REPO, "tools", "pnp.sh"), *args], cwd=REPO, capture_output=True, text=True,
                       timeout=timeout)
    return r.returncode, (r.stdout + r.stderr).strip()


def held():
    return [f[:-5] for f in os.listdir(os.path.join(REPO, ".pnp")) if f.endswith(".json") and not f.startswith(".")]


def clean_tree():
    r = subprocess.run(["git", "status", "--porcelain"], cwd=REPO, capture_output=True, text=True)
    return [l for l in r.stdout.splitlines() if not l.endswith(".pnp/")]


def release(gid, reason):
    code, out = pnp("release", gid, reason)
    g = json.load(open(os.path.join(REPO, ".pnp", gid + ".json")))["gap"]
    path = os.path.join(REPO, g.get("file") or "")
    tracked = subprocess.run(["git", "ls-files", "--error-unmatch", g.get("file") or "-"], cwd=REPO,
                             capture_output=True).returncode == 0
    if g.get("file") and os.path.exists(path) and not tracked:
        os.remove(path)
    os.rename(os.path.join(REPO, ".pnp", gid + ".json"), os.path.join(REPO, ".pnp", gid + ".done"))
    log("released %s (%s)" % (gid, reason))


def others_pr(gid):
    """Open pull requests by other agents titled exactly gid (the desk can lag GitHub by minutes)."""
    r = subprocess.run(["gh", "pr", "list", "--repo", "open-goat/pequalnp-proofs", "--state", "open", "--search",
                        gid + " in:title", "--json", "number,title,author", "--jq",
                        '.[] | select(.title == "%s" and .author.login != "sadeghja1070") | .number' % gid],
                       capture_output=True, text=True)
    return [n for n in r.stdout.split() if n.isdigit()]


def mark_done(gid):
    src = os.path.join(REPO, ".pnp", gid + ".json")
    if os.path.exists(src):
        os.rename(src, os.path.join(REPO, ".pnp", gid + ".done"))


def recover():
    """Undo what a crash or a kill can leave behind: another branch checked out, a lease held, an
    untracked proof file in the fork. Only untracked files under Outside/ are ever deleted."""
    subprocess.run(["git", "checkout", "-q", "main"], cwd=REPO)
    for gid in held():
        log("recovering: handing back %s" % gid)
        release(gid, "other")
    st = subprocess.run(["git", "status", "--porcelain", "--untracked-files=all"], cwd=REPO, capture_output=True, text=True)
    for line in st.stdout.splitlines():
        path = line[3:]
        if line.startswith("?? ") and re.fullmatch(r"lean/PEqualNP/Outside/L_meta_(\d+|scratch_\w+)\.lean", path):
            log("recovering: removing untracked %s" % path)
            os.remove(os.path.join(REPO, path))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--interval", type=float, default=45)
    ap.add_argument("--max-hours", type=float, default=3)
    ap.add_argument("--submit", action="store_true")
    a = ap.parse_args()
    stop_at = time.time() + a.max_hours * 3600
    recover()
    if clean_tree():
        sys.exit("the fork has changes that are not ours to remove: %s" % clean_tree())
    while time.time() < stop_at:
        if os.path.exists(os.path.join(HERE, "PAUSE")):
            time.sleep(60); continue  # remove solver/PAUSE to resume
        code, out = pnp("next", "--level", "solid", "--kind", "prove", timeout=120)
        m = re.search(r"^STEP\s+(L-[a-z]+-\d+) - (.*)$", out, re.M)
        if code == 120:
            log("STOP notice from the project: " + out.splitlines()[-1]); return 0  # 0: do not restart
        if not m:
            log("no step: " + (out.splitlines()[-1] if out else str(code)))
            time.sleep(a.interval); continue
        gid, title = m.group(1), m.group(2)
        g = json.load(open(os.path.join(REPO, ".pnp", gid + ".json")))["gap"]
        t = re.search(r"Nat\.testBit \((\d+) \* 2 \^ 32 \+ (\d+)\)", g.get("statement", ""))
        if t and g["statement"] == "¬ (" + STMT.format(hi=t.group(1), lo=t.group(2)) + ")":
            # a 'False:' twin: race for its true twin while nobody has sent a pull request for it
            log("%s: 'False:' twin; racing for its true twin" % gid)
            r = subprocess.run([sys.executable, "-I", os.path.join(HERE, "race.py"), gid], capture_output=True, text=True)
            for line in r.stdout.strip().splitlines()[-4:]:
                log("  race: " + line)
            if r.returncode == 0:
                pos = "L-meta-%d" % (int(gid.rsplit("-", 1)[1]) - 1)
                if not a.submit:
                    log("READY %s: checked and held. Submit with: tools/pnp.sh submit %s" % (pos, pos))
                    return 0
                prs = others_pr(pos)
                if prs:
                    log("%s: another agent's pull request is already open (#%s); not sending ours" % (pos, ", #".join(prs)))
                    release(pos, "other"); time.sleep(a.interval); continue
                code, out = pnp("submit", pos, timeout=600)
                log("%s submit: %s" % (pos, out[-500:]))
                subprocess.run(["git", "checkout", "-q", "main"], cwd=REPO)
                if code == 0:
                    mark_done(pos)
                else:  # e.g. another agent's pull request came first: give the lease back, drop the file
                    release(pos, "other")
                time.sleep(a.interval); continue
            if r.returncode == 3:
                release(gid, "statement_seems_false")  # its true twin is ours, checked by Lean
            for h in held():
                if h == gid or h == "L-meta-%d" % (int(gid.rsplit("-", 1)[1]) - 1):
                    release(h, "other")
            time.sleep(a.interval); continue
        if not (t and g["statement"] == STMT.format(hi=t.group(1), lo=t.group(2))):
            log("%s is not a direction-3 claim: %s" % (gid, title[:90]))
            release(gid, "other")
            time.sleep(a.interval); continue
        log("%s: direction-3 positive claim, table %s %s; generating" % (gid, t.group(1), t.group(2)))
        # keep the lease alive while the witness search runs (it can take ~10 minutes at 10 gates)
        stop_beats = threading.Event()

        def beats():
            while not stop_beats.wait(240):
                c, o = pnp("beat", gid)
                if "STOP" in o:
                    log("%s: desk says stop: %s" % (gid, o.splitlines()[-1])); return
        threading.Thread(target=beats, daemon=True).start()
        gen = subprocess.run([sys.executable, "-I", os.path.join(HERE, "gen_dir3.py"), "--json",
                              os.path.join(REPO, ".pnp", gid + ".json"), "--timeout", "1200"],
                             capture_output=True, text=True)
        stop_beats.set()
        log((gen.stdout.strip() or gen.stderr.strip()[-300:]).splitlines()[-1])
        if not gen.stdout.startswith("PROOF"):
            release(gid, "other")
            time.sleep(a.interval); continue
        code, out = pnp("beat", gid)
        if "STOP" in out:
            log("%s: lease withdrawn while generating: %s" % (gid, out.splitlines()[-1]))
            release(gid, "other"); continue
        code, out = pnp("check", gid, timeout=1800)
        log("%s check: %s" % (gid, out.splitlines()[-1] if out else code))
        if code != 0:
            log(out[-1500:])
            release(gid, "other"); continue
        if not a.submit:
            log("READY %s: checked and held. Submit with: tools/pnp.sh submit %s" % (gid, gid))
            return 0
        prs = others_pr(gid)
        if prs:
            log("%s: another agent's pull request is already open (#%s); not sending ours" % (gid, ", #".join(prs)))
            release(gid, "other"); time.sleep(a.interval); continue
        code, out = pnp("submit", gid, timeout=600)
        log("%s submit: %s" % (gid, out[-500:]))
        subprocess.run(["git", "checkout", "-q", "main"], cwd=REPO)
        if code == 0:
            mark_done(gid)
        else:  # e.g. another agent's pull request came first: give the lease back, drop the file
            release(gid, "other")
        time.sleep(a.interval)
    log("time limit reached")
    return 0


if __name__ == "__main__":
    sys.exit(main())
