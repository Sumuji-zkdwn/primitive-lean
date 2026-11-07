#!/usr/bin/env bash
# Re-check the direct derivations against the initial layer only (Elastica + All.lean).
# Requires linear_input/lean_check/All.lean from a successful proof run.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
W="${DERIV_WORK:-$ROOT/lean/.lake/derivation}"
mkdir -p "$W"
cp "$ROOT/linear_input/lean_check/All.lean" "$W/InitialLayer.lean"
cp "$ROOT/tools/deps/derivation/DirectDerivation.lean" "$W/"
cd "$ROOT/lean"
lake env lean --root="$W" -o "$W/InitialLayer.olean" "$W/InitialLayer.lean" > "$W/initial.log"
lake env sh -c "LEAN_PATH=\$LEAN_PATH:$W lean --trust=0 --root=$W -o $W/DirectDerivation.olean $W/DirectDerivation.lean"
printf 'import DirectDerivation\n#print axioms DirectDerivation.original_potential_formula\n#print axioms DirectDerivation.original_gradient_formula\n' > "$W/Audit.lean"
lake env sh -c "LEAN_PATH=\$LEAN_PATH:$W lean --trust=0 $W/Audit.lean"
