#!/usr/bin/env python3
"""Generate a Lean proof for a 'direction 3' positive step of pequalnp.com:

  for the monotone six-input f with table HI * 2^32 + LO, every AND/OR/NOT circuit of fan-in at
  most two has an AND/OR circuit no larger.

Method (from the accepted project proof L_meta_12230, Apache-2.0): a circuit with a NOT gate has
at most size-1 binary gates; fixing one input to false removes at least one more; a search the
kernel runs (`search B rows5 = false`) shows the five-input restriction needs more than B binary
gates even with free complements.  So size >= B + 3 = m, the size of the AND/OR witness.

usage:
  gen_dir3.py --json <.pnp/L-meta-N.json> [--out FILE]          statement, module from the lease
  gen_dir3.py --table HI LO --module L_meta_N [--out FILE]       statement derived from the table
Prints a one-line verdict; exits 1 when no proof of this shape was found."""
import argparse, json, os, random, re, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from leansearch import search, words  # noqa: E402

STMT = ("∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit ({hi} * 2 ^ 32 + {lo}) "
        "(∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, "
        "PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = "
        "Nat.testBit ({hi} * 2 ^ 32 + {lo}) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)")


def die(msg):
    print("NO PROOF: " + msg)
    sys.exit(1)


def find_witness(hi, lo, s, timeout, cores=12):
    """An AND/OR circuit with exactly s gates, by the C search split over `cores` processes; the
    first one found stops the rest. None when every part finished without one, or on timeout."""
    exe = os.path.join(HERE, "minckt")
    if not os.path.exists(exe) or os.path.getmtime(exe) < os.path.getmtime(exe + ".c"):
        subprocess.run(["cc", "-O3", "-march=native", "-o", exe, exe + ".c"], check=True)
    procs = [subprocess.Popen([exe, "0", str(s), str(cores), str(p), str(hi), str(lo), str(p + 1)], stdout=subprocess.PIPE, text=True)
             for p in range(cores)]
    found, start = None, time.time()
    try:
        while procs and found is None and time.time() - start < timeout:
            for p in list(procs):
                if p.poll() is not None:
                    out = p.stdout.read()
                    hit = [l for l in out.splitlines() if l.startswith("FOUND")]
                    if hit:
                        found = hit[0]
                    procs.remove(p)
            time.sleep(0.05)
    finally:
        for p in procs:
            p.kill()
    if not found:
        return None, not procs  # exhausted: every part finished without a circuit
    return [(m.group(2), int(m.group(3)), int(m.group(4)))
            for m in re.finditer(r"w(\d+)=(and|or)\(w(\d+),w(\d+)\)", found)], False


def largest_rejecting(W, cap=9):
    """Largest B <= cap with search B W = false (search is monotone in B), or -1."""
    best = -1
    for B in range(0, cap + 1):
        if search(B, W):
            break
        best = B
    return best


def evaluate(gates, x):
    w = [(x >> i) & 1 for i in range(6)]
    for op, a, b in gates:
        w.append(w[a] & w[b] if op == "and" else w[a] | w[b])
    return w[-1]


def restrict(f, idx):
    """Table of y -> f(insAt idx false y) on five inputs."""
    t = 0
    for y in range(32):
        x = (y & ((1 << idx) - 1)) | ((y >> idx) << (idx + 1))
        t |= f(x) << y
    return t


def pair_sets(t5, tries=300, seed=1):
    T = [r for r in range(32) if t5 >> r & 1]
    N = [r for r in range(32) if not t5 >> r & 1]
    exact = [(a, b) for a in T for b in N]
    if len(exact) <= 64:
        yield "exact", exact
        return
    tt = lambda r: t5 >> r & 1
    mins = [r for r in T if all(not tt(r & ~(1 << i)) for i in range(5) if r >> i & 1)]
    maxf = [r for r in N if all(tt(r | 1 << i) for i in range(5) if not r >> i & 1)]
    adj = []
    for t in mins:
        for i in range(5):
            if t >> i & 1:
                adj.append((t, t & ~(1 << i)))
    for f in maxf:
        for i in range(5):
            if not f >> i & 1:
                adj.append((f | 1 << i, f))
    adj = list(dict.fromkeys(adj))
    cross = [(a, b) for a in mins for b in maxf if (a, b) not in adj]
    if len(adj) <= 64:
        yield "adjacent+cross", (adj + cross)[:64]
    rng = random.Random(seed)
    for _ in range(tries):
        base = adj if len(adj) <= 48 else rng.sample(adj, 48)
        rest = [p for p in exact if p not in base]
        yield "random", base + rng.sample(rest, min(64 - len(base), len(rest)))


def lean_witness(gates):
    items = ["⟨.%s, [%d, %d]⟩" % (op, a, b) for op, a, b in gates]
    lines, cur = [], []
    for it in items:
        cur.append(it)
        if len(cur) == 4:
            lines.append(", ".join(cur)); cur = []
    if cur:
        lines.append(", ".join(cur))
    return "⟨[" + ",\n    ".join(lines) + "], %d⟩" % (6 + len(gates) - 1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--json")
    ap.add_argument("--table", nargs=2, type=int)
    ap.add_argument("--module")
    ap.add_argument("--out")
    ap.add_argument("--timeout", type=float, default=900, help="seconds for the first witness search")
    a = ap.parse_args()
    args_timeout = a.timeout
    if a.json:
        g = json.load(open(a.json))["gap"]
        stmt, module = g["statement"], g["module"].split(".")[-1]
        m = re.search(r"Nat\.testBit \((\d+) \* 2 \^ 32 \+ (\d+)\)", stmt)
        if not m:
            die("not a six-input table statement")
        hi, lo = int(m.group(1)), int(m.group(2))
        if stmt != STMT.format(hi=hi, lo=lo):
            die("statement is not the direction-3 positive shape")
        out = a.out or os.path.join(HERE, "..", "pequalnp-proofs", g["file"])
    else:
        hi, lo = a.table
        module = a.module
        stmt = STMT.format(hi=hi, lo=lo)
        out = a.out or os.path.join(HERE, "out", module + ".lean")
    T = hi * 2 ** 32 + lo
    f = lambda r: (T >> r) & 1
    if not all(f(r) <= f(r | 1 << i) for r in range(64) for i in range(6)):
        die("f is not monotone")
    t0 = time.time()
    # 1. The strongest kernel-checkable bound: for each input fixed to false, the largest B whose
    #    search rejects on some sample of 64 (true row, false row) pairs.
    best = None  # (Bmax, idx, how, P, t5, ydiff, y0, y1)
    for idx in range(6):
        t5 = restrict(f, idx)
        if t5 in (0, (1 << 32) - 1):
            continue
        ydiff = next((y for y in range(32) if f((y & ((1 << idx) - 1)) | ((y >> idx) << (idx + 1)))
                      != f((y & ((1 << idx) - 1)) | ((y >> idx) << (idx + 1)) | 1 << idx)), None)
        if ydiff is None:
            continue
        y0 = next(y for y in range(32) if not t5 >> y & 1)
        y1 = next(y for y in range(32) if t5 >> y & 1)
        for n, (how, P) in enumerate(pair_sets(t5)):
            if n >= 40:
                break
            W = words(5, P)
            if len(set(W)) < 5:
                continue
            Bmax = largest_rejecting(W)
            if best is None or Bmax > best[0]:
                best = (Bmax, idx, how, P, t5, ydiff, y0, y1)
    if best is None or best[0] < 0:
        die("no usable restriction")
    Bmax, idx, how, P, t5, ydiff, y0, y1 = best
    # 2. The smallest AND/OR witness, sizes upward: a size below the minimum must be exhausted (only
    #    the one just below costs anything), the minimum itself stops at the first circuit found.
    gates = None
    for s in range(1, Bmax + 4):
        g, exhausted = find_witness(hi, lo, s, timeout=args_timeout)
        if g is not None:
            gates = g
            break
        if not exhausted:
            die("witness search at size %d timed out after %.0fs" % (s, args_timeout))
    if gates is None:
        die("every AND/OR circuit needs more than %d gates, beyond the kernel bound (B at most %d)" % (Bmax + 3, Bmax))
    if not all(evaluate(gates, x) == f(x) for x in range(64)):
        die("witness check failed (search bug)")
    m = len(gates)
    B = m - 3
    W = words(5, P)
    assert not search(B, W)
    text = open(os.path.join(HERE, "template_dir3.lean"), encoding="utf-8").read()
    rows = "[" + ",\n   ".join("0x%032x" % w for w in W) + "]"
    for k, v in (("{{MOD}}", module), ("{{STMT}}", "(" + stmt + ")"), ("{{B}}", str(B)),
                 ("{{F5}}", str(t5)), ("{{ROWS5}}", rows), ("{{HI}}", str(hi)), ("{{LO}}", str(lo)),
                 ("{{IDX}}", str(idx)), ("{{YDIFF}}", str(ydiff)), ("{{Y0}}", str(y0)),
                 ("{{Y1}}", str(y1)), ("{{WITNESS}}", lean_witness(gates)), ("{{M}}", str(m))):
        text = text.replace(k, v)
    assert "{{" not in text
    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
    open(out, "w", encoding="utf-8").write(text)
    print("PROOF: %s m=%d B=%d (Bmax %d) idx=%d pairs=%s(%d) in %.0fs -> %s"
          % (module, m, B, Bmax, idx, how, len(P), time.time() - t0, out))


if __name__ == "__main__":
    main()
