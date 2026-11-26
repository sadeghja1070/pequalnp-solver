#!/usr/bin/env python3
"""Lean proofs for circuit steps whose proof is a computation, read from the statement itself.

Two shapes:
  explicit   the statement names a concrete circuit and asks facts Lean can decide (Monotone2 or
             FanInTwo, its size, Represents, its value on every input): one tactic per condition.
  exists     ∃ C : Circuit, conditions...: the function to compute is read from the conditions
             (an OR of ANDs of inputs, an edge list, a table, a count threshold, or Represents of
             a bipartite graph); a SAT solver (CaDiCaL, shipped with Lean) finds a circuit meeting
             the side conditions (AND/OR only, or with NOT; at most k gates; none dead; NOT rules).

The official statement is pasted into the theorem verbatim, so a condition read wrongly can only
make the Lean check fail, never prove something else. Conditions this file does not recognise
make it skip the step.

usage: gen_circ.py --id L-meta-N --statement-file F [--out FILE] [--timeout S]
       gen_circ.py --json <.pnp/L-meta-N.json> [--out FILE]
Prints one verdict line (PROOF / NO PROOF / SKIP)."""
import argparse, json, os, re, subprocess, sys, time, threading

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gen_find import cadical  # noqa: E402

E = "∃ C : PEqualNP.CircuitLowerBounds.Circuit, "
OPEQ = "let _ := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq\n    decide"
OPEN, CLOSE = "([{⟨", ")]}⟩"


def split_and(s):
    """Top-level conjuncts of s (not inside brackets)."""
    out, depth, cur, i = [], 0, [], 0
    while i < len(s):
        ch = s[i]
        if ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            depth -= 1
        if depth == 0 and s.startswith(" ∧ ", i):
            out.append("".join(cur).strip()); cur = []; i += 3; continue
        cur.append(ch); i += 1
    out.append("".join(cur).strip())
    return out


def unparen(c):
    """c without one pair of outer parentheses enclosing all of it."""
    if c.startswith("(") and c.endswith(")"):
        depth = 0
        for i, ch in enumerate(c):
            depth += ch in OPEN
            depth -= ch in CLOSE
            if depth == 0 and i < len(c) - 1:
                return c
        return c[1:-1]
    return c


def tactic(c):
    if c.startswith("PEqualNP.MetaComplexity.Monotone2 "):
        return "simp [PEqualNP.MetaComplexity.Monotone2]"
    if c.startswith("PEqualNP.MetaComplexity.FanInTwo "):
        return "simp [PEqualNP.MetaComplexity.FanInTwo]"
    if "GateOp.not" in c or "g.op =" in c:
        return OPEQ
    return "decide +kernel"


# ---- the function a circuit must compute: rows {input bits: value} over `n` inputs ----

MAXN = 12  # more inputs than this: too many rows for the SAT encoding and for decide


def rows_full(n, f):
    if n > MAXN:
        return None
    return n, {r: f([(r >> i) & 1 for i in range(n)]) for r in range(1 << n)}


def read_function(c):
    """(n, rows) when c fixes the circuit's value on inputs, else None."""
    u = unparen(c)
    m = re.fullmatch(r"∀ x : Fin (\d+) → Bool, C\.eval \(List\.ofFn x\) = \(fun (\w+) : Fin (\d+) → Bool => (.*)\) x", u)
    if m and m.group(1) == m.group(3):
        n, v, body = int(m.group(1)), m.group(2), m.group(4)
        terms = []
        for t in body.split(" || "):
            t = t[1:-1] if t.startswith("(") and t.endswith(")") else t
            lits = t.split(" && ")
            idx = []
            for l in lits:
                mm = re.fullmatch(re.escape(v) + r" (\d+)", l)
                if not mm or int(mm.group(1)) >= n:
                    return None
                idx.append(int(mm.group(1)))
            terms.append(idx)
        return rows_full(n, lambda x: int(any(all(x[i] for i in t) for t in terms)))
    m = re.fullmatch(r"∀ x : Fin (\d+) → Bool, \(C\.eval \(List\.ofFn x\) = true ↔ ∃ u v : Fin \1, \(u\.val, v\.val\) ∈ "
                     r"\(\[([0-9, ()]*)\] : List \(ℕ × ℕ\)\) ∧ x u = true ∧ x v = true\)", u)
    if m:
        n = int(m.group(1))
        es = [(int(a), int(b)) for a, b in re.findall(r"\((\d+), (\d+)\)", m.group(2))]
        if any(a >= n or b >= n for a, b in es):
            return None
        return rows_full(n, lambda x: int(any(x[a] and x[b] for a, b in es)))
    m = re.fullmatch(r"∀ x : Fin (\d+) → Bool, C\.eval \(List\.ofFn x\) = PEqualNP\.MetaComplexity\.tableFun \1 "
                     r"\(\(\[([01, ]*)\] : List ℕ\)\.map \(fun b => b == 1\)\) x", u)
    if m:
        n, bits = int(m.group(1)), [int(b) for b in m.group(2).split(", ")]
        if n > MAXN or len(bits) != 1 << n:
            return None
        return n, {r: bits[r] for r in range(1 << n)}
    m = re.fullmatch(r"∀ x : Fin (\d+) → Bool, C\.eval \(List\.ofFn x\) = Nat\.testBit (\(\d+ \* 2 \^ 32 \+ \d+\)|\d+) "
                     r"\(∑ i : Fin \1, if x i then 2 \^ \(i : ℕ\) else 0\)", u)
    if m:
        n, t = int(m.group(1)), m.group(2)
        if n > MAXN:
            return None
        mm = re.fullmatch(r"\((\d+) \* 2 \^ 32 \+ (\d+)\)", t)
        T = int(mm.group(1)) * 2 ** 32 + int(mm.group(2)) if mm else int(t)
        return n, {r: (T >> r) & 1 for r in range(1 << n)}
    m = re.fullmatch(r"∀ x : Fin (\d+) → Bool, C\.eval \(List\.ofFn x\) = decide \((\d+) ≤ \(List\.ofFn x\)\.count true\)", u)
    if m:
        n, k = int(m.group(1)), int(m.group(2))
        return rows_full(n, lambda x: int(sum(x) >= k))
    m = re.fullmatch(r"∀ i j : Fin (\d+), C\.eval \(List\.ofFn fun (\w+) : Fin \1 => decide \(\2 = i ∨ \2 = j\)\) = "
                     r"\((\d+) : ℕ\)\.testBit \((\d+) \* min i\.val j\.val \+ max i\.val j\.val\)", u)
    if m:  # the two-lit function of a graph: inputs with one or two of the n wires on
        n, M, K = int(m.group(1)), int(m.group(3)), int(m.group(4))
        if n > 2 * MAXN:
            return None
        return n, {(1 << a) | (1 << b): (M >> (K * a + b)) & 1 for a in range(n) for b in range(a, n)}
    m = re.fullmatch(r"PEqualNP\.Represents\.Represents \(fun u v : Fin (\d+) => (.*)\) C", u)
    if m:
        n, body = int(m.group(1)), m.group(2)
        if 2 * n > 2 * MAXN:
            return None
        mm = re.fullmatch(r"\((\d+) : ℕ\)\.testBit \((\d+) \* u\.val \+ v\.val\)", body)
        if mm:
            M, K = int(mm.group(1)), int(mm.group(2))
            A = lambda a, b: (M >> (K * a + b)) & 1
        elif body == "decide (u ≠ v)":
            A = lambda a, b: int(a != b)
        else:
            return None
        # inputs: n left wires then n right wires; rows only where exactly one of each is on
        return 2 * n, {(1 << a) | (1 << (n + b)): A(a, b) for a in range(n) for b in range(n)}
    return None


REP = "PEqualNP.Represents.RepSizeAtMost "
TOKEN = re.compile(r"\s*(decide|[uv]\.val|[uv]|\d+|[()+*/%<>=≠≤≥∧∨¬])")
PY = {"decide": "", "u.val": "u", "v.val": "v", "/": "//", "=": "==", "≠": "!=", "≤": "<=", "≥": ">=",
      "∧": " and ", "∨": " or ", "¬": " not "}


def graph(body, n, m):
    """A(a, b) for the Lean body of `fun u v => body` (Nat arithmetic on u.val and v.val, comparisons,
    ∧ ∨ ¬, decide), or None when the body uses anything else. No subtraction (Nat truncates) and no
    arithmetic on bare u or v (Fin wraps around): those are refused rather than read wrongly."""
    mm = re.fullmatch(r"\((\d+) : ℕ\)\.testBit \((\d+) \* u\.val \+ v\.val\)", body)
    if mm:  # a graph given by the bits of a mask
        M, K = int(mm.group(1)), int(mm.group(2))
        return {(a, b): (M >> (K * a + b)) & 1 for a in range(n) for b in range(m)}
    toks, i = [], 0
    while i < len(body):
        mm = TOKEN.match(body, i)
        if not mm:
            return None
        toks.append(mm.group(1)); i = mm.end()
    for j, t in enumerate(toks):
        if t in ("u", "v") and any(x in "+*/%" for x in toks[max(0, j - 1):j] + toks[j + 1:j + 2]):
            return None
    expr = " ".join(PY.get(t, t) for t in toks).strip()
    try:
        code = compile(expr, "<graph>", "eval")
        return {(a, b): int(bool(eval(code, {"__builtins__": {}}, {"u": a, "v": b}))) for a in range(n) for b in range(m)}
    except Exception:
        return None


def read_graph(st):
    """(n, m, k, A) for `RepSizeAtMost (fun u v : Fin n => body) k` (or with (u : Fin n) (v : Fin m))."""
    mm = re.fullmatch(re.escape(REP) + r"\(fun (?:u v : Fin (\d+)|\(u : Fin (\d+)\) \(v : Fin (\d+)\)) => (.*)\) (\d+)", st)
    if not mm:
        return None
    n = int(mm.group(1) or mm.group(2)); m = int(mm.group(1) or mm.group(3))
    if n + m > 48:
        return None
    A = graph(mm.group(4), n, m)
    return None if A is None else (n, m, int(mm.group(5)), A)


def rep_size(mod, st, timeout, parse_only=False):
    """RepSizeAtMost A k: a SAT-found AND/OR circuit of at most k gates on n + m wires, right on the
    n * m inputs with one vertex on each side (all Represents asks)."""
    r = read_graph(st)
    if r is None:
        return None, "SKIP: graph not recognised"
    n, m, k, A = r
    rows = {(1 << a) | (1 << (n + b)): v for (a, b), v in A.items()}
    if parse_only:
        return None, "PARSED: %d by %d graph, k=%d" % (n, m, k)
    gates, no = solve(n + m, k, rows, dict(allow_not=False, none_dead=False, some_not=False, not_on_gate=False),
                      timeout, mod)
    if not gates:
        return None, "NO PROOF: UNSAT at every size up to %d" % k if no else "NO PROOF: no circuit found in %.0fs" % timeout
    assert all(evaluate(gates, n + m, r) == v for r, v in rows.items())
    g = ", ".join("⟨.%s, [%s]⟩" % (op, ", ".join(map(str, ins))) for op, ins in gates)
    body = ("  unfold PEqualNP.Represents.RepSizeAtMost\n"
            "  refine ⟨⟨[%s], %d⟩, ?_, ?_, ?_⟩\n"
            "  · simp [PEqualNP.MetaComplexity.Monotone2]\n"
            "  · decide\n"
            "  · decide +kernel\n") % (g, n + m + len(gates) - 1)
    return HEADER + "theorem PEqualNP.Outside.%s : %s := by\n%s" % (mod, st, body), \
        "represents, %d by %d graph, %d gates (k=%d)" % (n, m, len(gates), k)


# ---- SAT ----

def encode(n, s, rows, allow_not, none_dead, some_not, not_on_gate, sym=True):
    nv = [0]
    def new():
        nv[0] += 1
        return nv[0]
    cls = []
    def add(*lits):
        out = []
        for l in lits:
            if l is True:
                return
            if l is not False:
                out.append(l)
        cls.append(out)
    def one(vs):
        add(*vs)
        for i in range(len(vs)):
            for j in range(i + 1, len(vs)):
                add(-vs[i], -vs[j])
    A = [new() for _ in range(s)]; O = [new() for _ in range(s)]
    N = [new() for _ in range(s)] if allow_not else [False] * s
    s1 = [[new() for _ in range(n + j)] for j in range(s)]
    s2 = [[new() for _ in range(n + j)] for j in range(s)]
    for j in range(s):
        one([A[j], O[j]] + ([N[j]] if allow_not else [])); one(s1[j]); one(s2[j])
        for a in range(n + j):
            for b in range(a + 1):
                add(-s1[j][a], -s2[j][b], N[j])
            if allow_not:
                add(-N[j], -s1[j][a], s2[j][a])
    for j in range(s - 2 if sym else 0):  # canonical greedy-min-key order before the output (see gen_find.py)
        nb = s2[j + 1][n + j]
        for u in range(n + j):
            for v in range(u):
                add(-s2[j][u], -s2[j + 1][v], nb)
        for w in range(n + j):
            for u in range(n + j):
                for v in range(u):
                    add(-s2[j][w], -s2[j + 1][w], -s1[j][u], -s1[j + 1][v])
    def lit(v, pos):
        if isinstance(v, bool):
            return v if pos else not v
        return v if pos else -v
    for r, val in rows.items():
        x = [(r >> i & 1) == 1 for i in range(n)] + [new() for _ in range(s)]
        for j in range(s):
            g, v1, v2 = x[n + j], new(), new()
            for a in range(n + j):
                add(-s1[j][a], lit(x[a], False), v1); add(-s1[j][a], lit(x[a], True), -v1)
                add(-s2[j][a], lit(x[a], False), v2); add(-s2[j][a], lit(x[a], True), -v2)
            add(-A[j], -g, v1); add(-A[j], -g, v2); add(-A[j], g, -v1, -v2)
            add(-O[j], g, -v1); add(-O[j], g, -v2); add(-O[j], -g, v1, v2)
            if allow_not:
                add(-N[j], -g, -v1); add(-N[j], g, v1)
        add(x[n + s - 1] if val else -x[n + s - 1])
    if none_dead:
        for j in range(s - 1):
            add(*[v for i in range(j + 1, s) for v in (s1[i][n + j], s2[i][n + j])])
    if not_on_gate:
        z = []
        for j in range(s):
            for a in range(n, n + j):
                zz = new(); z.append(zz)
                add(-zz, N[j]); add(-zz, s1[j][a])
                add(-N[j], -s1[j][a], -N[a - n])
        add(*z)
    elif some_not:
        add(*N)
    def decode(model):
        gates = []
        for j in range(s):
            a = next(w for w in range(n + j) if model[s1[j][w]])
            b = next(w for w in range(n + j) if model[s2[j][w]])
            op = "and" if model[A[j]] else "or" if model[O[j]] else "not"
            gates.append((op, [a] if op == "not" else [a, b]))
        return gates
    return nv[0], cls, decode


def solve(n, s, rows, opts, timeout, tag):
    """(gates, unsat) for a circuit of s gates. Two encodings race: without the symmetry clauses
    CaDiCaL finds circuits quickly; with them it proves that none exists sooner. Both are sound,
    so the first decisive answer stands and the other run is stopped."""
    runs = []
    try:
        for sym in (False, True):
            nv, cls, decode = encode(n, s, rows, sym=sym, **opts)
            path = os.path.join(HERE, "out", "circ_%s_%d_%d_%d_%d.cnf" % (tag, s, sym, os.getpid(), threading.get_ident()))
            with open(path, "w") as f:
                f.write("p cnf %d %d\n" % (nv, len(cls)))
                f.writelines(" ".join(map(str, c)) + " 0\n" for c in cls)
            out = open(path + ".out", "w")
            p = subprocess.Popen([cadical(), "-q", "-t", str(max(1, int(timeout))), path], stdout=out,
                                 stderr=subprocess.DEVNULL)
            runs.append((p, path, nv, decode, out))
        deadline = time.time() + timeout + 10
        while time.time() < deadline:
            live = 0
            for p, path, nv, decode, out in runs:
                if p.poll() is None:
                    live += 1
                    continue
                if p.returncode == 20:
                    return None, True
                if p.returncode == 10:
                    out.flush()
                    model = [False] * (nv + 1)
                    for line in open(path + ".out"):
                        if line.startswith("v "):
                            for v in map(int, line[2:].split()):
                                if v > 0:
                                    model[v] = True
                    return decode(model), False
            if not live:
                break
            time.sleep(0.2)
        return None, False
    finally:
        for p, path, nv, decode, out in runs:
            if p.poll() is None:
                p.kill(); p.wait()
            out.close()
            for f in (path, path + ".out"):
                if os.path.exists(f):
                    os.remove(f)


def evaluate(gates, n, r):
    w = [(r >> i) & 1 for i in range(n)]
    for op, ins in gates:
        a = [w[i] for i in ins]
        w.append(int(all(a)) if op == "and" else int(any(a)) if op == "or" else 1 - a[0])
    return w[-1]


# ---- the two shapes ----

HEADER = "import Mathlib\nimport PEqualNP.Defs\n\n"


def explicit(mod, st):
    if not ("{ gates := [" in st or "⟨[{ op :=" in st or "⟨[⟨" in st):
        return None, "SKIP: no concrete circuit"
    if st.startswith(("∀ C", "¬", "∃")) or re.match(r"∀ \(", st):
        return None, "SKIP: not a closed statement about a concrete circuit"
    parts = split_and(st)
    ok = (r"PEqualNP\.MetaComplexity\.(Monotone2|FanInTwo) \(", r"\(\{ gates := .*\)\.size (=|≤) \d+$",
          r"PEqualNP\.Represents\.Represents \(fun u v : Fin \d+ => .*\) \(\{ gates :=",
          r"∀ x : Fin \d+ → Bool, \(⟨\[")
    for p in parts:
        if not any(re.match(k, p, re.S) for k in ok):
            return None, "SKIP: condition not recognised: %s" % p[:80]
    if len(parts) == 1:
        body = "  %s\n" % tactic(parts[0]).replace("\n    ", "\n  ")
    else:
        body = "  refine ⟨%s⟩\n%s" % (", ".join(["?_"] * len(parts)), "".join("  · %s\n" % tactic(p) for p in parts))
    return HEADER + "theorem PEqualNP.Outside.%s : %s := by\n%s" % (mod, st, body), "explicit, %d conditions" % len(parts)


def exists(mod, st, timeout, parse_only=False):
    if not st.startswith(E):
        return None, "SKIP: not an ∃ C statement"
    parts = split_and(st[len(E):])
    n, rows, k, mono, fan, rb, dead, nng, some, someg = None, None, None, False, False, None, False, False, False, False
    for p in parts:
        u = unparen(p)
        if p == "PEqualNP.MetaComplexity.Monotone2 C":
            mono = True
        elif p == "PEqualNP.MetaComplexity.FanInTwo C":
            fan = True
        elif re.fullmatch(r"PEqualNP\.MetaComplexity\.NestedCover\.ReadsBack \d+ C", p):
            rb = int(p.split()[1])
        elif re.fullmatch(r"C\.size ≤ \d+", p):
            k = int(p.split()[-1])
        elif re.fullmatch(r"∀ j < C\.size, C\.output = (\d+) \+ j ∨ ∃ i < C\.size, j < i ∧ \1 \+ j ∈ \(C\.gates\.getD i "
                          r"⟨PEqualNP\.CircuitLowerBounds\.GateOp\.and, \[\]⟩\)\.inputs", u) or \
                re.fullmatch(r"∀ j : ℕ, j < C\.gates\.length → C\.output = (\d+) \+ j ∨ ∃ k : ℕ, k < C\.gates\.length ∧ j < k ∧ "
                             r"\1 \+ j ∈ \(C\.gates\.getD k ⟨PEqualNP\.CircuitLowerBounds\.GateOp\.and, \[\]⟩\)\.inputs", u):
            dead = True
        elif re.fullmatch(r"∀ g ∈ C\.gates, g\.op = PEqualNP\.CircuitLowerBounds\.GateOp\.not → (\d+) ≤ g\.inputs\.headD 0 → "
                          r"\(C\.gates\.getD \(g\.inputs\.headD 0 - \1\) ⟨PEqualNP\.CircuitLowerBounds\.GateOp\.and, \[\]⟩\)\.op ≠ "
                          r"PEqualNP\.CircuitLowerBounds\.GateOp\.not", u):
            nng = True
        elif re.fullmatch(r"∃ g ∈ C\.gates, g\.op = PEqualNP\.CircuitLowerBounds\.GateOp\.not ∧ g\.inputs\.length = 1", u):
            some = True
        elif re.fullmatch(r"∃ g ∈ C\.gates, g\.op = PEqualNP\.CircuitLowerBounds\.GateOp\.not ∧ \d+ ≤ g\.inputs\.headD 0", u):
            someg = True
        else:
            f = read_function(p)
            if f is None or rows is not None:
                return None, "SKIP: condition not recognised: %s" % p[:80]
            n, rows = f
    if rows is None or k is None or mono == fan:
        return None, "SKIP: missing the function, the size bound or the gate kinds"
    if rb is not None and rb != n:
        return None, "SKIP: ReadsBack on %d wires, function on %d" % (rb, n)
    if (nng or someg or some) and not fan:
        return None, "SKIP: NOT conditions on an AND/OR circuit"
    opts = dict(allow_not=fan, none_dead=dead, some_not=some, not_on_gate=someg)
    if parse_only:
        return None, "PARSED: %d inputs, %d rows, k=%d" % (n, len(rows), k)
    t0, gates, unsat = time.time(), None, []
    for s in range(k, 0, -1):
        left = timeout - (time.time() - t0)
        if left <= 0:
            break
        gates, no = solve(n, s, rows, opts, left, mod)
        if gates or not no:
            break
        unsat.append(s)
    if not gates:
        if unsat and unsat[-1] == 1:
            return None, "NO PROOF: UNSAT at every size up to %d" % k
        return None, "NO PROOF: no circuit found in %.0fs" % (time.time() - t0)
    assert all(evaluate(gates, n, r) == v for r, v in rows.items())
    holes = ", ".join(["?_"] * len(parts))
    g = ", ".join("⟨.%s, [%s]⟩" % (op, ", ".join(map(str, ins))) for op, ins in gates)
    body = "  refine ⟨⟨[%s], %d⟩, %s⟩\n%s" % (g, n + len(gates) - 1, holes, "".join("  · %s\n" % tactic(p) for p in parts))
    return HEADER + "theorem PEqualNP.Outside.%s : %s := by\n%s" % (mod, st, body), \
        "exists, %d inputs, %d gates (k=%d)" % (n, len(gates), k)


def parses(st):
    """True when generate() would try this statement (a cheap check, no SAT)."""
    flat = unparen(re.sub(r"\s+", " ", st).strip())
    if flat.startswith(E):
        return exists("X", flat, 0, parse_only=True)[1].startswith("PARSED")
    if flat.startswith(REP):
        return read_graph(flat) is not None
    return explicit("X", flat)[0] is not None


def generate(gid, st, timeout=600):
    """Parse a whitespace-normalised copy; the theorem states the statement exactly as given."""
    mod = gid.replace("-", "_")
    flat = unparen(re.sub(r"\s+", " ", st).strip())  # some statements come wrapped in one pair of brackets
    if flat.startswith(E):
        lean, why = exists(mod, flat, timeout)
    elif flat.startswith(REP):
        lean, why = rep_size(mod, flat, timeout)
    else:
        lean, why = explicit(mod, flat)
    if lean is not None:
        lean = lean.replace(" : %s := by" % flat, " : %s := by" % st, 1)
    return lean, why


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--json")
    ap.add_argument("--id")
    ap.add_argument("--statement-file")
    ap.add_argument("--out")
    ap.add_argument("--timeout", type=float, default=600)
    a = ap.parse_args()
    if a.json:
        g = json.load(open(a.json))["gap"]
        gid, st = g["id"], g["statement"]
        out = a.out or os.path.join(HERE, "..", "pequalnp-proofs", g["file"])
    else:
        gid, st = a.id, open(a.statement_file, encoding="utf-8").read().strip()
        out = a.out or os.path.join(HERE, "out", gid.replace("-", "_") + ".lean")
    t0 = time.time()
    lean, why = generate(gid, st, a.timeout)
    if lean is None:
        print(why); sys.exit(1)
    open(out, "w", encoding="utf-8").write(lean)
    print("PROOF: %s %s in %.0fs -> %s" % (gid, why, time.time() - t0, out))


if __name__ == "__main__":
    main()
