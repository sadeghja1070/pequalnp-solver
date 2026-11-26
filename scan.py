#!/usr/bin/env python3
"""List the open steps of the meta program from the site's public data export
(https://data.pequalnp.com, the files the site itself reads; not the desk) and say which ones a
generator here can prove.

Files there are immutable (their name carries their content hash), so each lemma file is fetched
once and kept in out/lemmas/. Only open steps (status conjecture) are fetched, a few at a time.

usage: scan.py [--workers 4] [--json out/scan.json]
Prints counts per kind; --json writes [{id, kind, statement}] for the steps we can prove."""
import argparse, json, os, re, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gen_dir3 import STMT  # noqa: E402
import gen_find  # noqa: E402

DATA = "https://data.pequalnp.com/"
CACHE = os.path.join(HERE, "out", "lemmas")


def fetch(rel, path=None, fresh=False):
    """GET a file of the export with curl (keeps the user agent ordinary); cached when path is given."""
    if path and os.path.exists(path) and not fresh:
        return json.load(open(path))
    r = subprocess.run(["curl", "-sf", "--max-time", "30", DATA + rel], capture_output=True, text=True)
    if r.returncode != 0:
        raise IOError("%s: curl exit %d" % (rel, r.returncode))
    v = json.loads(r.stdout)
    if path:
        tmp = path + ".tmp"
        open(tmp, "w").write(r.stdout)
        os.replace(tmp, path)
    return v


def kind_of_statement(st):
    """'dir3' or 'find:<kind>' when a generator here proves exactly this statement, else None."""
    t = re.search(r"Nat\.testBit \((\d+) \* 2 \^ 32 \+ (\d+)\)", st)
    if t and st == STMT.format(hi=t.group(1), lo=t.group(2)):
        return "dir3"
    for kind in ("midnot", "tie6", "tie5"):
        try:
            if gen_find.statement(kind, *gen_find.parse(kind, st)) == st:
                return "find:" + kind
        except (AttributeError, ValueError, IndexError):
            pass
    return None


def open_steps(program="meta", status="j"):
    """[(id, ref)] of the program's steps with the given status letter (j: conjecture, open)."""
    head = fetch("head.json")
    ov = fetch(head["files"]["map"])
    prog = [p for p in ov["programs"] if p["key"] == program][0]
    nodes = fetch(prog["file"])["nodes"]
    return [("L-%s-%d" % (program, n[0]), n[3]) for n in nodes if n[1] == status]


def programs():
    """The keys of every program in the export (meta, gct, clb, pcx, lib, alg, ...)."""
    head = fetch("head.json")
    return [p["key"] for p in fetch(head["files"]["map"])["programs"]]


def scan(workers=4, programs=("meta",)):
    os.makedirs(CACHE, exist_ok=True)
    steps = [s for p in programs for s in open_steps(p)]

    def one(s):
        gid, ref = s
        for attempt in range(3):  # the export's server drops a connection now and then
            try:
                d = fetch("data/lemma/%s.%s.json" % (gid, ref), os.path.join(CACHE, "%s.%s.json" % (gid, ref)))
                break
            except (IOError, ValueError) as e:
                if attempt == 2:
                    return gid, None, ""
                time.sleep(2)
        st = d.get("formal_statement") or ""
        return gid, kind_of_statement(st), st
    with ThreadPoolExecutor(workers) as ex:
        return list(ex.map(one, steps))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--json", default=os.path.join(HERE, "out", "scan.json"))
    a = ap.parse_args()
    t0 = time.time()
    res = scan(a.workers)
    counts = {}
    for gid, kind, _ in res:
        counts[kind] = counts.get(kind, 0) + 1
    ours = [{"id": gid, "kind": kind, "statement": st} for gid, kind, st in res if kind]
    json.dump(ours, open(a.json, "w"), ensure_ascii=False, indent=0)
    print("open steps %d in %.0fs; ours: %s" % (len(res), time.time() - t0,
          ", ".join("%s %d" % (k, n) for k, n in sorted(counts.items(), key=lambda kv: str(kv[0])) if k)))


if __name__ == "__main__":
    main()
