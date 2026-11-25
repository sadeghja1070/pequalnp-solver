#!/bin/sh
# test_build.sh HI LO TAG : generate a proof for the table under module L_meta_scratch_<TAG>, build it with Lean, delete it.
set -e
here=$(cd "$(dirname "$0")" && pwd); repo="$here/../pequalnp-proofs"
mod="L_meta_scratch_$3"; out="$repo/lean/PEqualNP/Outside/$mod.lean"
# never touch a file the repository tracks
if (cd "$repo" && git ls-files --error-unmatch "lean/PEqualNP/Outside/$mod.lean" >/dev/null 2>&1); then echo "refusing: $mod is tracked"; exit 1; fi
python3 -I "$here/gen_dir3.py" --table "$1" "$2" --module "$mod" --out "$out" --timeout "${GEN_TIMEOUT:-900}" || exit 1
cd "$repo/lean"
start=$(date +%s)
if lake build "PEqualNP.Outside.$mod" > "$here/out/$mod.build.log" 2>&1; then echo "LEAN OK $mod in $(( $(date +%s) - start ))s"; else echo "LEAN FAILED $mod (log: $here/out/$mod.build.log)"; tail -20 "$here/out/$mod.build.log"; fi
cp "$out" "$here/out/$mod.lean"; rm -f "$out"
