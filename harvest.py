#!/usr/bin/env python3
"""Find open steps ahead of the desk and prove them locally, so the autopilot can lease each with
`pnp.sh next --proof-of` (allowed for a step we hold a checked proof of) and submit it.

Discovery: the site's public data export (scan.py) lists every step with its statement; the desk
(/desk/step, a few seconds apart) says which are still live, since the export also keeps steps
the fleet stood down. Proving: the generator that fits the statement (gen_dir3, gen_find,
gen_circ) writes the file under the step's own module name into out/proven/, and Lean checks it
there with `lake env lean` (outside the fork, so several checks run at once and the fork's
working tree is never touched). Submitting is the autopilot's job (one step at a time).

State lives in out/harvest.json: {step: {kind, state, why, at}}, states
  new -> live (desk open or leased) -> proven | failed | unsat | dead (desk: not open)
  proven -> submitted | lost (someone else got there first) | refused.

usage (by hand): harvest.py --once [--workers 4]   one discovery pass and the proofs it starts"""
import argparse, json, os, queue, re, subprocess, sys, threading, time

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "pequalnp-proofs"))
sys.path.insert(0, HERE)
import gen_circ, gen_find, scan  # noqa: E402

STATE = os.path.join(HERE, "out", "harvest.json")
PROVEN = os.path.join(HERE, "out", "proven")
PRIORITY = {"dir3": 0, "explicit": 1, "rep": 1, "exists": 2, "find": 3}
DESK_GAP = 5.0          # seconds between this module's desk requests
DEAD_RECHECK = 24 * 3600  # a stood-down step is asked about again after a day


def now():
    return time.time()


class Harvester:
    def __init__(self, log, workers=4, refresh_every=300):
        self.log, self.workers, self.refresh_every = log, workers, refresh_every
        self.lock = threading.Lock()
        self.db = json.load(open(STATE)) if os.path.exists(STATE) else {}
        self.q = queue.PriorityQueue()
        self.last_desk = 0.0
        self.busy = set()  # steps a worker is proving right now
        os.makedirs(PROVEN, exist_ok=True)

    # ---- bookkeeping ----
    def save(self):
        with self.lock:
            tmp = STATE + ".tmp"
            json.dump(self.db, open(tmp, "w"), indent=0)
            os.replace(tmp, STATE)

    def mark(self, gid, state, why=""):
        with self.lock:
            e = self.db.setdefault(gid, {})
            e.update(state=state, why=why[:300], at=now())
        self.save()

    def ready(self):
        """Proven steps not yet submitted, best first."""
        with self.lock:
            items = [(PRIORITY.get(e.get("kind"), 9), e.get("at", 0), gid) for gid, e in self.db.items() if e.get("state") == "proven"]
        return [gid for _, _, gid in sorted(items)]

    def statement(self, gid):
        return self.db.get(gid, {}).get("statement")

    def proof_path(self, gid):
        return os.path.join(PROVEN, gid.replace("-", "_") + ".lean")

    # ---- discovery ----
    def classify(self, st):
        k = scan.kind_of_statement(st)
        if k == "dir3":
            return "dir3"
        if k:
            return "find"
        flat = gen_circ.unparen(re.sub(r"\s+", " ", st).strip())
        if flat.startswith(gen_circ.E):
            _, why = gen_circ.exists("X", flat, 0, parse_only=True)
            return "exists" if why.startswith("PARSED") else None
        if flat.startswith(gen_circ.REP):
            return "rep" if gen_circ.read_graph(flat) else None
        lean, _ = gen_circ.explicit("X", flat)
        return "explicit" if lean else None

    def desk_state(self, gid):
        wait = self.last_desk + DESK_GAP - now()
        if wait > 0:
            time.sleep(wait)
        self.last_desk = now()
        r = subprocess.run(["curl", "--proto", "=https", "-fsS", "-m", "15", "-G", "https://pequalnp.com/desk/step",
                            "--data-urlencode", "gap=" + gid], capture_output=True, text=True)
        try:
            return json.loads(r.stdout).get("state") or "unknown"
        except ValueError:
            return "unknown"

    def discover(self):
        """One pass over the export: new steps we can prove get their desk state asked; live ones queue."""
        try:
            res = scan.scan(workers=4)
        except Exception as e:  # network trouble: try again next round
            self.log("harvest: export scan failed: %s" % e)
            return
        found = 0
        for gid, _, st in res:
            if not st:
                continue
            e = self.db.get(gid)
            if e and e.get("state") not in ("new", "dead"):
                continue
            if e and e.get("state") == "dead" and now() - e.get("at", 0) < DEAD_RECHECK:
                continue
            if e is None:
                kind = self.classify(st)
                if not kind:
                    continue
                with self.lock:
                    self.db[gid] = {"kind": kind, "state": "new", "statement": st, "at": now()}
            s = self.desk_state(gid)
            if s in ("open", "leased"):
                self.mark(gid, "live", s)
                self.q.put((PRIORITY[self.db[gid]["kind"]], int(gid.rsplit("-", 1)[1]), gid))
                found += 1
            elif s in ("not_open", "pr_open"):
                self.mark(gid, "dead", s)
        # steps left live by an earlier run (killed mid-proof) queue again
        with self.lock:
            stale = [gid for gid, e in self.db.items() if e.get("state") == "live"]
        for gid in stale:
            self.q.put((PRIORITY[self.db[gid]["kind"]], int(gid.rsplit("-", 1)[1]), gid))
        self.log("harvest: export has %d open steps; %d live ones of ours queued, %d proven waiting"
                 % (len(res), found, len(self.ready())))

    # ---- proving ----
    def generate(self, gid, kind, st, out):
        mod = gid.replace("-", "_")
        if kind == "dir3":
            t = re.search(r"Nat\.testBit \((\d+) \* 2 \^ 32 \+ (\d+)\)", st)
            r = subprocess.run([sys.executable, "-I", os.path.join(HERE, "gen_dir3.py"), "--table", t.group(1), t.group(2),
                                "--module", mod, "--out", out, "--timeout", "1200"], capture_output=True, text=True)
            return r.stdout.startswith("PROOF"), (r.stdout.strip() or r.stderr.strip()[-200:])
        if kind == "find":
            fk = scan.kind_of_statement(st).split(":")[1]
            n, k, table = gen_find.parse(fk, st)
            r = subprocess.run([sys.executable, "-I", os.path.join(HERE, "gen_find.py"), "--kind", fk, "--n", str(n), "--k", str(k),
                                "--table", str(table), "--module", mod, "--out", out, "--timeout", "900"],
                               capture_output=True, text=True)
            return r.stdout.startswith("PROOF"), (r.stdout.strip() or r.stderr.strip()[-200:])
        lean, why = gen_circ.generate(gid, st, timeout=600)
        if lean is None:
            return False, why
        open(out, "w", encoding="utf-8").write(lean)
        return True, why

    def prove(self, gid):
        e = self.db[gid]
        out = self.proof_path(gid)
        ok, why = self.generate(gid, e["kind"], e["statement"], out)
        if not ok:
            self.mark(gid, "unsat" if "UNSAT" in why else "failed", why.splitlines()[-1] if why else "")
            return
        t0 = now()
        try:
            r = subprocess.run(["lake", "env", "lean", out], cwd=os.path.join(REPO, "lean"), capture_output=True,
                               text=True, timeout=1500)
            ok = r.returncode == 0
            err = (r.stdout + r.stderr).strip()
        except subprocess.TimeoutExpired:
            ok, err = False, "lean timed out"
        if ok:
            self.mark(gid, "proven", "%s; Lean %.0fs" % (why.splitlines()[-1], now() - t0))
            self.log("harvest: proved %s locally (%s)" % (gid, self.db[gid]["why"]))
        else:
            self.mark(gid, "failed", "lean: " + " ".join(l for l in err.splitlines() if "error" in l)[:250])

    def worker(self):
        while True:
            _, _, gid = self.q.get()
            with self.lock:
                if self.db.get(gid, {}).get("state") != "live" or gid in self.busy:
                    continue
                self.busy.add(gid)
            try:
                self.prove(gid)
            except Exception as ex:  # one bad step must not stop the pool
                self.mark(gid, "failed", "%s: %s" % (type(ex).__name__, ex))
            finally:
                with self.lock:
                    self.busy.discard(gid)

    def run(self):
        for _ in range(self.workers):
            threading.Thread(target=self.worker, daemon=True).start()
        while True:
            self.discover()
            time.sleep(self.refresh_every)

    def start(self):
        threading.Thread(target=self.run, daemon=True).start()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--once", action="store_true")
    ap.add_argument("--workers", type=int, default=4)
    a = ap.parse_args()
    log = lambda m: print(time.strftime("%H:%M:%S"), m, flush=True)
    h = Harvester(log, a.workers)
    for _ in range(a.workers):
        threading.Thread(target=h.worker, daemon=True).start()
    h.discover()
    while a.once and (not h.q.empty() or h.busy):
        time.sleep(10)
    log("harvest: proven waiting: %s" % ", ".join(h.ready()))


if __name__ == "__main__":
    main()
