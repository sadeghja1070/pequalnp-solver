# Proof generators (pequalnp.com)

Builds Lean proofs for two kinds of steps of the P vs NP desk: the "direction 3" positive claims
and small "find" steps. The autopilot takes steps from the desk and runs the right generator.

## Direction-3 claims

The step says:

> for the monotone six-input f with table `HI * 2^32 + LO`, each AND/OR/NOT circuit of fan-in at
> most two has an AND/OR one no larger.

## How a proof works

The proof argument is the project's accepted file `L_meta_12230` (Apache-2.0), turned into a
template with only the per-function parts as placeholders:

1. A circuit with no NOT gate is already an AND/OR circuit.
2. A circuit with a NOT gate has at most `size - 1` binary gates. Fixing one input to false
   removes at least one more (`drop_one_var`).
3. A search the Lean kernel runs (`search B rows5 = false`) shows the five-input restriction
   needs more than `B` binary gates even with free complements. It works on 64 sampled
   (true row, false row) pairs, so it is a sound relaxation.
4. So `size >= B + 3`, the size of an AND/OR witness checked by `decide +kernel`.

## Find steps

Three desk templates ask for a small AND/OR/NOT circuit of fan-in at most two that computes a given
monotone function and uses NOT:

- `obja-midnot-9c`: 5 or 6 inputs, at most k gates, none dead, no NOT reads a NOT, some NOT reads a gate.
- `tie6-find`: 6 inputs, at most k gates (the AND/OR size), some one-input NOT gate.
- `tie5-find3`: 5 inputs, at most k gates, none dead, some one-input NOT gate.

`gen_find.py` rebuilds the statement from its parameters and refuses any difference from the
desk's text. It encodes "a circuit of exactly s gates" as SAT (gate order fixed to a canonical
topological order to remove reorderings) and solves it with the CaDiCaL that ships with the Lean
toolchain, trying s = k first, then smaller. A circuit found is re-checked in Python against the
statement's own conditions; the Lean proof is the circuit, `simp` for the gate kinds and `decide`
for the rest (the kernel for the truth table). UNSAT at every size means no such circuit with
binary gates on two different wires, so the step is handed back as `statement_seems_false`.

## Files

| File | Role |
|---|---|
| `minckt.c` | Exhaustive fan-in-2 circuit search on 6 inputs (AND/OR, or AND/OR/NOT), split over processes |
| `leansearch.py` | Exact Python mirror of the kernel search, to predict `search B rows5` before building |
| `make_template.py` | Makes `template_dir3.lean` from `L_meta_12230.lean`, asserting every placeholder's place |
| `gen_dir3.py` | Table (or lease JSON) to Lean file: picks the input to fix, the sample pairs, B, the witness |
| `test_build.sh` | Generate under a scratch module in the fork, `lake build` it, delete it |
| `race.py` | For a held "False:" twin L-meta-N: prove L-meta-(N-1), lease it with `--proof-of`, check it |
| `gen_find.py` | Find steps: lease JSON (or kind, n, k, table) to Lean file, by SAT |
| `build_scratch.sh` | Guard-check and `lake build` a generated `out/L_meta_scratch_*.lean` in the fork, then remove it |
| `autopilot.py` | Takes solid prove steps, runs the generator that fits, checks, submits; stops a generator when the desk withdraws its step |
| `launchd/` | Runs the autopilot as a launchd agent (`install.sh`, `uninstall.sh`; pause with `touch PAUSE`) |

## Use

```bash
python3 make_template.py ../pequalnp-proofs/lean/PEqualNP/Outside/L_meta_12230.lean template_dir3.lean
./test_build.sh HI LO TAG            # local trial, nothing sent
python3 gen_find.py --kind midnot --n 5 --k 10 --table 4169170944 --module L_meta_scratch_M10
./build_scratch.sh L_meta_scratch_M10   # guard + Lean build of that trial, nothing sent
python3 race.py L-meta-N             # stops before submit; add --submit to open the pull request
```
