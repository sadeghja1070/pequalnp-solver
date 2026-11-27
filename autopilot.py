#!/usr/bin/env python3
"""Ask the desk for solid prove steps and prove the ones this solver reads, several at once.

usage: autopilot.py [--interval 45] [--max-hours 3] [--submit] [--slots 4] [--battery-slots 2]
  Each round: `pnp.sh next --level solid --kind prove` (with --another while steps are held; the desk
  allows five at a time). A step a generator reads goes to a slot: its generator runs there, in
  parallel with the other slots, and writes the proof outside the fork. Everything that touches the
  fork's tree or git state (next, check, submit, release) runs one at a time under one lock; lease
  renewals go straight to the desk (POST /desk/beat), not through pnp.sh, whose beat would also
  rewrite FETCH_HEAD under a submit running in another slot.
  - a direction-3 positive claim: generate the proof from the lease (gen_dir3.py --json), renew the
    lease, `pnp.sh check`. Without --submit it stops there with the step checked and held; with
    --submit it runs `pnp.sh submit` and goes on.
  - a 'find' step (templates obja-midnot-9c, tie6-find, tie5-find3: a small circuit using NOT):
    gen_find.py --json, then the same check and submit. A SAT answer of "no such circuit" hands it
    back as statement_seems_false, a timeout as out_of_time.
  - a direction-3 'False:' twin: race for its true twin (race.py).
  - anything else: a battery of standard tactics (battery.py) in at most --battery-slots slots at
    once; if none closes it, or those slots are busy, it is handed back as `other`, which also keeps
    the desk from offering it to us again for an hour.
  While a generator runs the lease is renewed every 4 minutes; when the desk withdraws the step,
  the generator and its solver processes are stopped at once.
  The desk asks for one request every few seconds at most; rounds are --interval seconds apart.
Log lines go to stdout; a READY line names a checked step waiting for its pull request."""
import argparse, json, os, re, shutil, signal, subprocess, sys, threading, time

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "pequalnp-proofs"))
sys.path.insert(0, HERE)
from gen_dir3 import STMT  # noqa: E402
import gen_circ, gen_find  # noqa: E402
sys.path.insert(0, os.path.join(HERE, "pcx"))
import gen_pcx  # noqa: E402
from harvest import Harvester, desk_gate  # noqa: E402

BEAT = 240  # seconds between lease renewals while a generator runs
DESK = "https://pequalnp.com/desk"
MAX_HELD = 5  # the desk's limit on steps held at once
SLOTS = os.path.join(HERE, "out", "slots")  # proofs written by slots, before they go into the fork
FORK = threading.RLock()  # one fork-touching pnp.sh call at a time
ACTIVE = {}  # step -> kind, for the steps slots work on now
ACTIVE_LOCK = threading.Lock()


def log(msg):
    print(time.strftime("%H:%M:%S"), msg, flush=True)


def pnp(*args, timeout=None):
    desk_gate()
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


def kind_of(g):
    """'dir3' for a direction-3 positive claim, 'find' for a find step gen_find.py proves, else None."""
    st = g.get("statement", "")
    t = re.search(r"Nat\.testBit \((\d+) \* 2 \^ 32 \+ (\d+)\)", st)
    if t and st == STMT.format(hi=t.group(1), lo=t.group(2)):
        return "dir3"
    kind = gen_find.TEMPLATES.get((g.get("faithful_by_template") or {}).get("template"))
    if kind:
        try:
            if gen_find.statement(kind, *gen_find.parse(kind, st)) == st:
                return "find"
        except (AttributeError, ValueError):
            pass
    if gen_circ.parses(st):
        return "circ"
    r = gen_pcx.read_statement(st)
    if r:
        lines = gen_pcx.best(r[1], r[2])
        if lines and len(lines) <= r[3]:
            return "pcx"
    return None


def known_unsat(h, gid):
    """The harvester's verdict line when it already showed this step false (no circuit at any size)."""
    try:
        e = (h.db if h else json.load(open(os.path.join(HERE, "out", "harvest.json")))).get(gid) or {}
    except (OSError, ValueError):
        return None
    return e.get("why") if e.get("state") == "unsat" else None


def beat(gid):
    """Renew a lease straight at the desk (join.txt: POST /desk/beat?lease=<id>; a 410 means stop).
    (True, note) while the lease holds or the desk could not be reached; (False, why) when it is gone."""
    try:
        lease = json.load(open(os.path.join(REPO, ".pnp", gid + ".json")))["lease"]["id"]
    except (OSError, ValueError, KeyError, TypeError):
        return False, "no lease file here"
    if not re.fullmatch(r"[A-Za-z0-9-]{1,64}", str(lease)):
        return False, "unreadable lease id"
    desk_gate()
    r = subprocess.run(["curl", "--proto", "=https", "-sS", "-m", "15", "-X", "POST", DESK + "/beat?lease=" + lease],
                       capture_output=True, text=True)
    try:
        d = json.loads(r.stdout)
    except ValueError:
        return True, "no answer from the desk"
    if isinstance(d, dict) and isinstance(d.get("lease"), dict):
        return True, "lease until %s" % d["lease"].get("expires_at")
    return False, re.sub(r"[^ -~]", " ", str((d or {}).get("error") or "the lease is gone"))[:300]


def generate(gid, cmd):
    """Run a generator, renewing the lease while it works; if the desk withdraws the step, stop the
    generator and every process it started. Returns (stdout, stderr, withdrawn)."""
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, start_new_session=True)
    done, withdrawn = threading.Event(), threading.Event()

    def beats():
        while not done.wait(BEAT):
            ok, why = beat(gid)
            if not ok:
                log("%s: desk says stop: %s" % (gid, why))
                withdrawn.set()
                try:
                    os.killpg(p.pid, signal.SIGTERM)
                except ProcessLookupError:
                    pass
                return
    threading.Thread(target=beats, daemon=True).start()
    out, err = p.communicate()
    done.set()
    return out, err, withdrawn.is_set()


def submit_harvested(h, log_prefix="harvest"):
    """Lease one step the harvester proved, with `next --proof-of`, put the checked file in place,
    check it with pnp.sh and submit it. Returns "sent", "dropped" (lost, refused, failed) or None."""
    for gid in h.ready():
        st = h.desk_state(gid)
        if st not in ("open", "leased"):
            h.mark(gid, "lost", "desk: " + st); log("%s: %s is %s now; dropped" % (log_prefix, gid, st)); return "dropped"
        prs = others_pr(gid)
        if prs:
            h.mark(gid, "lost", "pull request #" + prs[0]); log("%s: %s already has #%s; dropped" % (log_prefix, gid, prs[0])); return "dropped"
        code, out = pnp("next", "--proof-of", gid, timeout=120)
        lease = os.path.join(REPO, ".pnp", gid + ".json")
        if not os.path.exists(lease):
            h.mark(gid, "refused", out.splitlines()[-1] if out else str(code))
            log("%s: the desk did not lease %s: %s" % (log_prefix, gid, h.db[gid]["why"])); return "dropped"
        g = json.load(open(lease))["gap"]
        text = open(h.proof_path(gid), encoding="utf-8").read()
        imports = re.findall(r"^import (\S+)", text, re.M)
        bad = [m for m in imports if not (m == "Mathlib" or m.startswith("Mathlib.") or m in (g.get("imports") or []))]
        if g["statement"] != h.statement(gid) or g["module"] != "PEqualNP.Outside." + gid.replace("-", "_") or bad:
            why = "imports %s not allowed" % bad if bad else "statement or module differs from the export"
            h.mark(gid, "failed", why); log("%s: %s: %s; handed back" % (log_prefix, gid, why))
            release(gid, "other"); return "dropped"
        open(os.path.join(REPO, g["file"]), "w", encoding="utf-8").write(text)
        code, out = pnp("check", gid, timeout=1800)
        if code != 0:
            h.mark(gid, "failed", "check: " + (out.splitlines()[-1] if out else str(code)))
            log("%s: %s check failed: %s" % (log_prefix, gid, out[-800:])); release(gid, "other"); return "dropped"
        code, out = pnp("submit", gid, timeout=600)
        log("%s: %s submit: %s" % (log_prefix, gid, out[-400:]))
        subprocess.run(["git", "checkout", "-q", "main"], cwd=REPO)
        if code == 0:
            mark_done(gid); h.mark(gid, "submitted", out.splitlines()[-1] if out else "")
        else:
            h.mark(gid, "failed", "submit: " + (out.splitlines()[-1] if out else str(code))); release(gid, "other")
            return "dropped"
        return "sent"
    return None


def recover():
    """Undo what a crash or a kill can leave behind: another branch checked out, a lease held, an
    untracked proof file in the fork. Only untracked files under Outside/ are ever deleted."""
    subprocess.run(["git", "checkout", "-q", "main"], cwd=REPO)
    # a slot's generator runs in its own session, so a restart of this agent leaves it (and its SAT
    # solvers) working for a step that is handed back below: stop each one's whole process group
    pg = subprocess.run(["pgrep", "-f", "--", "--out " + SLOTS + os.sep], capture_output=True, text=True)
    for pid in map(int, pg.stdout.split()):
        try:
            if os.getpgid(pid) == pid:
                log("recovering: stopping a leftover generator (pid %d)" % pid)
                os.killpg(pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
    for gid in held():
        log("recovering: handing back %s" % gid)
        release(gid, "other")
    st = subprocess.run(["git", "status", "--porcelain", "--untracked-files=all"], cwd=REPO, capture_output=True, text=True)
    for line in st.stdout.splitlines():
        path = line[3:]
        if line.startswith("?? ") and re.fullmatch(r"lean/PEqualNP/Outside/L_(meta_scratch_R\d+|[a-z]+_\d+)\.lean", path):
            log("recovering: removing untracked %s" % path)
            os.remove(os.path.join(REPO, path))


def finish(gid, path, a):
    """Under FORK: put a slot's proof in the fork, check it with pnp.sh and send it."""
    lease = os.path.join(REPO, ".pnp", gid + ".json")
    if not os.path.exists(lease):
        log("%s: no longer held; proof not sent" % gid); return
    g = json.load(open(lease))["gap"]
    ok, why = beat(gid)
    if not ok:
        log("%s: lease withdrawn while working: %s" % (gid, why)); release(gid, "other"); return
    shutil.copyfile(path, os.path.join(REPO, g["file"]))
    code, out = pnp("check", gid, timeout=1800)
    log("%s check: %s" % (gid, out.splitlines()[-1] if out else code))
    if code != 0:
        log(out[-1500:]); release(gid, "other"); return
    if not a.submit:
        log("READY %s: checked and held. Submit with: tools/pnp.sh submit %s" % (gid, gid)); return
    prs = others_pr(gid)
    if prs:
        log("%s: another agent's pull request is already open (#%s); not sending ours" % (gid, ", #".join(prs)))
        release(gid, "other"); return
    code, out = pnp("submit", gid, timeout=600)
    log("%s submit: %s" % (gid, out[-500:]))
    subprocess.run(["git", "checkout", "-q", "main"], cwd=REPO)
    if code == 0:
        mark_done(gid)
    else:  # e.g. another agent's pull request came first: give the lease back, drop the file
        release(gid, "other")


def slot(gid, kind, h, a):
    """One step, in its own thread: run its generator (lease renewed meanwhile), then finish under FORK."""
    lease = os.path.join(REPO, ".pnp", gid + ".json")
    out = os.path.join(SLOTS, gid.replace("-", "_") + ".lean")
    try:
        gens = {"dir3": ("gen_dir3.py", 1200), "circ": ("gen_circ.py", 1200), "find": ("gen_find.py", 1500),
                "battery": ("battery.py", 300), "pcx": (os.path.join("pcx", "gen_pcx.py"), 120)}
        prog, limit = gens[kind]
        cmd = [sys.executable, "-I", os.path.join(HERE, prog), "--json", lease, "--out", out, "--timeout", str(limit)]
        gout, gerr, withdrawn = generate(gid, cmd)
        if withdrawn:
            with FORK:
                release(gid, "other")
            return
        log("%s: %s" % (gid, (gout.strip() or gerr.strip()[-300:] or "generator gave no output").splitlines()[-1]))
        if not gout.startswith("PROOF"):
            reason = "other"
            if kind in ("find", "circ"):
                reason = "statement_seems_false" if "UNSAT at every size" in gout else "out_of_time"
                if h and gid in h.db and "UNSAT at every size" in gout:
                    h.mark(gid, "unsat", gout.strip().splitlines()[-1])
            with FORK:
                release(gid, reason)
            return
        with FORK:
            finish(gid, out, a)
    except Exception as ex:  # one bad step must not stop the others
        log("%s: slot failed: %s: %s" % (gid, type(ex).__name__, ex))
        with FORK:
            if os.path.exists(lease):
                release(gid, "other")
    finally:
        with ACTIVE_LOCK:
            ACTIVE.pop(gid, None)


def take_step(h, a):
    """Under FORK: ask the desk for one step and route it. Returns "stop" on the project's STOP notice."""
    another = ["--another"] if held() else []
    code, out = pnp("next", *another, "--level", "solid", "--kind", "prove", timeout=120)
    m = re.search(r"^STEP\s+(L-[a-z]+-\d+) - (.*)$", out, re.M)
    if code == 120:
        log("STOP notice from the project: " + out.splitlines()[-1]); return "stop"
    if not m:
        log("no step: " + (out.splitlines()[-1] if out else str(code))); return None
    gid, title = m.group(1), m.group(2)
    g = json.load(open(os.path.join(REPO, ".pnp", gid + ".json")))["gap"]
    t = re.search(r"Nat\.testBit \((\d+) \* 2 \^ 32 \+ (\d+)\)", g.get("statement", ""))
    if t and g["statement"] == "¬ (" + STMT.format(hi=t.group(1), lo=t.group(2)) + ")":
        # a 'False:' twin: race for its true twin while nobody has sent a pull request for it (rare; in line)
        log("%s: 'False:' twin; racing for its true twin" % gid)
        r = subprocess.run([sys.executable, "-I", os.path.join(HERE, "race.py"), gid], capture_output=True, text=True)
        for line in r.stdout.strip().splitlines()[-4:]:
            log("  race: " + line)
        pos = "L-meta-%d" % (int(gid.rsplit("-", 1)[1]) - 1)
        if r.returncode == 0:
            if not a.submit:
                log("READY %s: checked and held. Submit with: tools/pnp.sh submit %s" % (pos, pos)); return None
            prs = others_pr(pos)
            if prs:
                log("%s: another agent's pull request is already open (#%s); not sending ours" % (pos, ", #".join(prs)))
                release(pos, "other"); return None
            code, out = pnp("submit", pos, timeout=600)
            log("%s submit: %s" % (pos, out[-500:]))
            subprocess.run(["git", "checkout", "-q", "main"], cwd=REPO)
            if code == 0:
                mark_done(pos)
            else:
                release(pos, "other")
            return None
        if r.returncode == 3:
            release(gid, "statement_seems_false")  # its true twin is ours, checked by Lean
        for x in held():
            if x in (gid, pos) and x not in ACTIVE:
                release(x, "other")
        return None
    kind = kind_of(g)
    known = known_unsat(h, gid) if kind in ("find", "circ") else None
    if known:
        log("%s: already shown false here (%s); handing it back" % (gid, known[:120]))
        release(gid, "statement_seems_false"); return None
    if kind is None:
        with ACTIVE_LOCK:
            batteries = sum(1 for k in ACTIVE.values() if k == "battery")
        if not g.get("file") or not g.get("statement") or batteries >= a.battery_slots:
            log("%s is not a step this solver proves: %s" % (gid, title[:90]))
            release(gid, "other"); return None
        kind = "battery"
    # the slot writes its proof outside the fork; the skeleton next wrote would block other slots' submits
    path = os.path.join(REPO, g["file"])
    tracked = subprocess.run(["git", "ls-files", "--error-unmatch", g["file"]], cwd=REPO, capture_output=True).returncode == 0
    if os.path.exists(path) and not tracked:
        os.remove(path)
    log("%s: %s step (%s); slot %d of %d" % (gid, kind, title[:90], len(ACTIVE) + 1, a.slots))
    with ACTIVE_LOCK:
        ACTIVE[gid] = kind
    threading.Thread(target=slot, args=(gid, kind, h, a), daemon=True).start()
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--interval", type=float, default=45)
    ap.add_argument("--max-hours", type=float, default=3)
    ap.add_argument("--submit", action="store_true")
    ap.add_argument("--slots", type=int, default=4, help="desk steps worked on at once (the desk allows 5 held)")
    ap.add_argument("--battery-slots", type=int, default=2, help="of those, at most this many on the tactic battery")
    ap.add_argument("--harvest-workers", type=int, default=4, help="parallel local proofs of export steps (0: off)")
    ap.add_argument("--submit-gap", type=float, default=300, help="seconds between pull requests of harvested steps")
    a = ap.parse_args()
    a.slots = max(1, min(a.slots, MAX_HELD - 1))  # one lease kept free for a harvested --proof-of
    stop_at = time.time() + a.max_hours * 3600
    os.makedirs(SLOTS, exist_ok=True)
    recover()
    if clean_tree():
        sys.exit("the fork has changes that are not ours to remove: %s" % clean_tree())
    h, last_sent = None, 0.0
    if a.harvest_workers > 0 and a.submit:
        h = Harvester(log, a.harvest_workers)
        h.start()
    while time.time() < stop_at:
        if os.path.exists(os.path.join(HERE, "PAUSE")):
            time.sleep(60); continue  # remove solver/PAUSE to resume
        if h and time.time() - last_sent >= a.submit_gap and h.ready():
            with FORK:
                r = submit_harvested(h)
            if r == "sent":
                last_sent = time.time()
            if r:
                continue
        with ACTIVE_LOCK:
            busy = len(ACTIVE)
        if busy >= a.slots or len(held()) >= MAX_HELD:
            time.sleep(5); continue
        with FORK:
            if take_step(h, a) == "stop":
                return 0  # 0: do not restart
        time.sleep(a.interval)
    log("time limit reached; waiting for the slots to finish")
    while ACTIVE:
        time.sleep(10)
    return 0


if __name__ == "__main__":
    sys.exit(main())
