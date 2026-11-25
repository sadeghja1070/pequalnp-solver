# Direction-3 proof generator (pequalnp.com)

Builds Lean proofs for the "direction 3" positive steps of the P vs NP desk:

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

## Files

| File | Role |
|---|---|
| `minckt.c` | Exhaustive fan-in-2 circuit search on 6 inputs (AND/OR, or AND/OR/NOT), split over processes |
| `leansearch.py` | Exact Python mirror of the kernel search, to predict `search B rows5` before building |
| `make_template.py` | Makes `template_dir3.lean` from `L_meta_12230.lean`, asserting every placeholder's place |
| `gen_dir3.py` | Table (or lease JSON) to Lean file: picks the input to fix, the sample pairs, B, the witness |
| `test_build.sh` | Generate under a scratch module in the fork, `lake build` it, delete it |
| `race.py` | For a held "False:" twin L-meta-N: prove L-meta-(N-1), lease it with `--proof-of`, check it |

## Use

```bash
python3 make_template.py ../pequalnp-proofs/lean/PEqualNP/Outside/L_meta_12230.lean template_dir3.lean
./test_build.sh HI LO TAG            # local trial, nothing sent
python3 race.py L-meta-N             # stops before submit; add --submit to open the pull request
```
