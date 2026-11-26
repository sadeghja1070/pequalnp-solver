#!/usr/bin/env python3
"""Generate a Lean proof for a pequalnp.com 'find' step: some small AND/OR/NOT circuit of fan-in at
most two computes a given monotone function and uses NOT. Three desk templates:

  obja-midnot-9c  on n = 5 or 6 inputs (table as a 0/1 list), at most k gates, every gate read later
                  or the output, gates read only earlier wires, no NOT reads a NOT, some NOT reads a gate
  tie6-find       on 6 inputs (table HI * 2^32 + LO), at most k gates, some one-input NOT gate
  tie5-find3      on 5 inputs (table T), at most k gates, every gate read later or the output,
                  some one-input NOT gate

The answer is an object: a SAT encoding solved by CaDiCaL (shipped with the Lean toolchain) finds
the circuit, Python re-checks it against the statement's own conditions, and the Lean proof is the circuit plus
`decide` over all inputs. Every statement is rebuilt from its parameters and must equal the
desk's text exactly, so a change upstream skips the step instead of producing a wrong proof.

usage:
  gen_find.py --json <.pnp/L-meta-N.json> [--out FILE] [--timeout S]
  gen_find.py --kind midnot|tie6|tie5 --n N --k K --table T --module L_meta_X [--out FILE]
Prints one verdict line; exits 1 when no circuit was found in the time given."""
import argparse, json, os, re, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
CL = "PEqualNP.CircuitLowerBounds"
TEMPLATES = {"obja-midnot-9c": "midnot", "tie6-find": "tie6", "tie5-find3": "tie5"}

MIDNOT = ("∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ "
          "PEqualNP.MetaComplexity.NestedCover.ReadsBack @N C ∧ C.size ≤ @K ∧ (∀ x : Fin @N → Bool, "
          "C.eval (List.ofFn x) = PEqualNP.MetaComplexity.tableFun @N (([@L] : List ℕ).map (fun b => b == 1)) x) ∧ "
          "(∀ j < C.size, C.output = @N + j ∨ ∃ i < C.size, j < i ∧ @N + j ∈ "
          "(C.gates.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) ∧ "
          "(∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not → @N ≤ g.inputs.headD 0 → "
          "(C.gates.getD (g.inputs.headD 0 - @N) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).op ≠ "
          "PEqualNP.CircuitLowerBounds.GateOp.not) ∧ "
          "(∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ @N ≤ g.inputs.headD 0)")
TIE6 = ("∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ "
        "(∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1) ∧ C.size ≤ @K ∧ "
        "∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (@HI * 2 ^ 32 + @LO) "
        "(∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)")
TIE5 = ("∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ "
        "(∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1) ∧ "
        "(∀ j : ℕ, j < C.gates.length → C.output = 5 + j ∨ ∃ k : ℕ, k < C.gates.length ∧ j < k ∧ 5 + j ∈ "
        "(C.gates.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) ∧ C.size ≤ @K ∧ "
        "∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit @T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)")

LEAN = """import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.@MOD : @STMT := by
  refine ⟨⟨[@GATES], @OUT⟩, @HOLES⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
@PARTS"""
# The conditions after FanInTwo, in statement order: those comparing gate kinds need a decision
# procedure for GateOp equality, which the project keeps local (gateOpDecEq, as accepted proofs use
# it); the truth table is checked by the kernel.
OPEQ = "let _ := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq\n    decide"
PARTS = {"midnot": ["decide", "decide", "decide +kernel", "decide", OPEQ, OPEQ],
         "tie6": [OPEQ, "decide", "decide +kernel"],
         "tie5": [OPEQ, "decide", "decide", "decide +kernel"]}


def fill(t, **kw):
    for k, v in kw.items():
        t = t.replace("@" + k, str(v))
    assert "@" not in t.replace("@[", ""), t
    return t


def statement(kind, n, k, table):
    if kind == "midnot":
        return fill(MIDNOT, N=n, K=k, L=", ".join(str(table >> r & 1) for r in range(1 << n)))
    if kind == "tie6":
        return fill(TIE6, K=k, HI=table >> 32, LO=table & 0xffffffff)
    return fill(TIE5, K=k, T=table)


def parse(kind, st):
    """(n, k, table) read from the desk's statement; the caller checks it rebuilds exactly."""
    k = int(re.search(r"C\.size ≤ (\d+)", st).group(1))
    if kind == "midnot":
        n = int(re.search(r"ReadsBack (\d+) C", st).group(1))
        bits = [int(b) for b in re.search(r"\(\[([01, ]*)\] : List ℕ\)", st).group(1).split(", ")]
        if len(bits) != 1 << n:
            raise ValueError("table length %d for %d inputs" % (len(bits), n))
        return n, k, sum(b << r for r, b in enumerate(bits))
    if kind == "tie6":
        m = re.search(r"Nat\.testBit \((\d+) \* 2 \^ 32 \+ (\d+)\)", st)
        return 6, k, int(m.group(1)) * 2 ** 32 + int(m.group(2))
    return 5, k, int(re.search(r"Nat\.testBit (\d+) \(∑", st).group(1))


def cadical():
    """The SAT solver that ships with the Lean toolchain (the newest one installed)."""
    import glob
    found = sorted(glob.glob(os.path.expanduser("~/.elan/toolchains/*/bin/cadical")), key=os.path.getmtime)
    if not found:
        sys.exit("NO PROOF: cadical not found under ~/.elan/toolchains")
    return found[-1]


def encode(kind, n, s, table):
    """CNF: a circuit of exactly s AND/OR/NOT gates (gate j reads wires below n + j, a binary gate
    two different wires, a NOT one), output the last gate, computing table; with kind's extra
    conditions. Returns (clauses, decode) where decode(model) gives the gates."""
    nv = [0]
    def new():
        nv[0] += 1
        return nv[0]
    cls = []
    def add(*lits):  # a literal may be a bool constant: True satisfies the clause, False drops out
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
    R, W = 1 << n, n + s
    A = [new() for _ in range(s)]; O = [new() for _ in range(s)]; N = [new() for _ in range(s)]
    s1 = [[new() for _ in range(n + j)] for j in range(s)]
    s2 = [[new() for _ in range(n + j)] for j in range(s)]
    for j in range(s):
        one([A[j], O[j], N[j]]); one(s1[j]); one(s2[j])
        for a in range(n + j):
            for b in range(a + 1):  # a binary gate reads two wires a < b
                add(-s1[j][a], -s2[j][b], N[j])
            add(-N[j], -s1[j][a], s2[j][a])  # a NOT reads one wire, named by both selectors
    x = [[(r >> i & 1) == 1 for i in range(n)] + [new() for _ in range(s)] for r in range(R)]
    def lit(v, pos):
        return v if isinstance(v, bool) and pos else (not v) if isinstance(v, bool) else (v if pos else -v)
    for r in range(R):
        for j in range(s):
            g, v1, v2 = x[r][n + j], new(), new()
            for a in range(n + j):
                add(-s1[j][a], lit(x[r][a], False), v1); add(-s1[j][a], lit(x[r][a], True), -v1)
                add(-s2[j][a], lit(x[r][a], False), v2); add(-s2[j][a], lit(x[r][a], True), -v2)
            add(-A[j], -g, v1); add(-A[j], -g, v2); add(-A[j], g, -v1, -v2)
            add(-O[j], g, -v1); add(-O[j], g, -v2); add(-O[j], -g, v1, v2)
            add(-N[j], -g, -v1); add(-N[j], g, v1)
        add(x[r][W - 1] if table >> r & 1 else -x[r][W - 1])
    # Symmetry: gates in a greedy-min-key topological order (key: the larger wire read, then the
    # smaller), so a gate that does not read the gate just before it has a key no smaller than it.
    # Every circuit has such an order among the gates before the output, so this removes
    # reorderings only, never a circuit. The output is the last gate and cannot move, so the pair
    # (s - 2, s - 1) is left out: ordering it too wrongly excluded circuits whose output does not
    # read the gate just before it (possible when dead gates are allowed, as in tie6).
    for j in range(s - 2):
        nb = s2[j + 1][n + j]  # gate j+1 reads gate j (its larger wire is the newest one)
        for u in range(n + j):
            for v in range(u):
                add(-s2[j][u], -s2[j + 1][v], nb)
        for w in range(n + j):
            for u in range(n + j):
                for v in range(u):
                    add(-s2[j][w], -s2[j + 1][w], -s1[j][u], -s1[j + 1][v])
    if kind in ("midnot", "tie5"):  # none dead: every gate but the last is read by a later gate
        for j in range(s - 1):
            add(*[v for i in range(j + 1, s) for v in (s1[i][n + j], s2[i][n + j])])
    if kind == "midnot":  # some NOT reads a gate; no NOT reads a NOT
        z = []
        for j in range(s):
            for a in range(n, n + j):
                zz = new(); z.append(zz)
                add(-zz, N[j]); add(-zz, s1[j][a])
                add(-N[j], -s1[j][a], -N[a - n])
        add(*z)
    else:  # some NOT gate
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


def search(kind, n, s, table, timeout, tag):
    """Solve the CNF for exactly s gates with CaDiCaL. Returns (gates, unsat)."""
    nv, cls, decode = encode(kind, n, s, table)
    path = os.path.join(HERE, "out", "find_%s_%d.cnf" % (tag, s))
    with open(path, "w") as f:
        f.write("p cnf %d %d\n" % (nv, len(cls)))
        f.writelines(" ".join(map(str, c)) + " 0\n" for c in cls)
    r = subprocess.run([cadical(), "-q", "-t", str(max(1, int(timeout))), path], capture_output=True, text=True)
    os.remove(path)
    if r.returncode == 20:
        return None, True
    if r.returncode != 10:
        return None, False
    model = [False] * (nv + 1)
    for line in r.stdout.splitlines():
        if line.startswith("v "):
            for v in map(int, line[2:].split()):
                if v > 0:
                    model[v] = True
    return decode(model), False


def check(kind, n, k, table, gates):
    """The statement's conditions, evaluated directly on the circuit (output: the last gate)."""
    out = n + len(gates) - 1
    assert 0 < len(gates) <= k
    for j, (op, ins) in enumerate(gates):
        assert op in ("and", "or", "not") and len(ins) == (1 if op == "not" else 2)
        assert all(i < n + j for i in ins)  # reads only earlier wires
        if kind != "tie6":  # none dead (tie6 does not ask it)
            assert out == n + j or any(n + j in gates[i][1] for i in range(j + 1, len(gates)))
    for r in range(1 << n):
        w = [r >> i & 1 for i in range(n)]
        for op, ins in gates:
            a = [w[i] for i in ins]
            w.append(int(all(a)) if op == "and" else int(any(a)) if op == "or" else 1 - a[0])
        assert w[out] == table >> r & 1, "row %d" % r
    nots = [ins[0] for op, ins in gates if op == "not"]
    assert nots
    if kind == "midnot":
        assert any(i >= n for i in nots)
        assert all(i < n or gates[i - n][0] != "not" for i in nots)


def lean_gates(gates):
    return ", ".join("⟨.%s, [%s]⟩" % (op, ", ".join(map(str, ins))) for op, ins in gates)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--json")
    ap.add_argument("--kind", choices=("midnot", "tie6", "tie5"))
    ap.add_argument("--n", type=int)
    ap.add_argument("--k", type=int)
    ap.add_argument("--table", type=int)
    ap.add_argument("--module")
    ap.add_argument("--out")
    ap.add_argument("--timeout", type=float, default=1500)
    a = ap.parse_args()
    t0 = time.time()
    if a.json:
        g = json.load(open(a.json))["gap"]
        kind = TEMPLATES.get((g.get("faithful_by_template") or {}).get("template"))
        if not kind:
            print("NO PROOF: not a find template this generator knows"); sys.exit(1)
        try:
            n, k, table = parse(kind, g["statement"])
        except (AttributeError, ValueError) as e:
            print("NO PROOF: statement not in the expected shape (%s)" % e); sys.exit(1)
        mod = g["module"].rsplit(".", 1)[1]
        if statement(kind, n, k, table) != g["statement"]:
            print("NO PROOF: statement differs from the %s template" % kind); sys.exit(1)
        out = a.out or os.path.join(HERE, "..", "pequalnp-proofs", g["file"])
    else:
        kind, n, k, table, mod = a.kind, a.n, a.k, a.table, a.module
        out = a.out or os.path.join(HERE, "out", mod + ".lean")
    gates, unsat = None, []
    # Most likely size first: k (the AND/OR size plus the NOT, or the tie); then smaller ones.
    for s in range(k, 0, -1):
        left = a.timeout - (time.time() - t0)
        if left <= 0:
            break
        gates, no = search(kind, n, s, table, left, mod)
        if gates or not no:
            break
        unsat.append(s)
    if not gates and unsat and unsat[-1] == 1:
        print("NO PROOF: no circuit of at most %d gates (UNSAT at every size, binary gates on two different wires)" % k)
        sys.exit(1)
    if not gates:
        print("NO PROOF: no circuit found for %s n=%d k=%d table=%d in %.0fs" % (kind, n, k, table, time.time() - t0))
        sys.exit(1)
    check(kind, n, k, table, gates)
    st = statement(kind, n, k, table)
    parts = PARTS[kind]
    lean = fill(LEAN, MOD=mod, STMT=st, GATES=lean_gates(gates), OUT=n + len(gates) - 1,
                HOLES=", ".join(["?_"] * (len(parts) + 1)), PARTS="".join("  · %s\n" % p for p in parts))
    open(out, "w", encoding="utf-8").write(lean)
    print("PROOF: %s %s n=%d size=%d (k=%d) in %.0fs -> %s" % (mod, kind, n, len(gates), k, time.time() - t0, out))


if __name__ == "__main__":
    main()
