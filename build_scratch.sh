#!/bin/sh
# build_scratch.sh MODULE : guard-check and Lean-build out/MODULE.lean (a scratch module, name starting
# L_meta_scratch_) inside the fork, then take it out again. Do not run while the autopilot works.
set -eu
here=$(cd "$(dirname "$0")" && pwd -P); repo="$here/../pequalnp-proofs"
mod="${1:?module}"
case "$mod" in L_meta_scratch_*) ;; *) echo "refusing: $mod is not a scratch module"; exit 1 ;; esac
rel="lean/PEqualNP/Outside/$mod.lean"
if (cd "$repo" && git ls-files --error-unmatch "$rel" >/dev/null 2>&1); then echo "refusing: $mod is tracked"; exit 1; fi
cp "$here/out/$mod.lean" "$repo/$rel"
# The guard wants a step's own file name: check a copy renamed to a made-up step number.
sed "s/$mod/L_meta_999999/g" "$here/out/$mod.lean" > "$here/out/L_meta_999999.lean"
echo "guard: $(python3 -I "$here/out/guard.py" "$here/out/L_meta_999999.lean" lean/PEqualNP/Outside/L_meta_999999.lean "$here/out/fake_state.json" 2>&1 | tail -3)"
start=$(date +%s)
if (cd "$repo/lean" && lake build "PEqualNP.Outside.$mod" > "$here/out/$mod.build.log" 2>&1); then
  echo "LEAN OK $mod in $(( $(date +%s) - start ))s"
else
  echo "LEAN FAILED $mod (log: out/$mod.build.log)"; tail -30 "$here/out/$mod.build.log"
fi
rm -f "${repo:?}/${rel:?}"
