#!/usr/bin/env bash
set -euo pipefail

# Compile a real proof combining a primitive-lean supplement with imported
# LANA iut declarations.  Never alter the original projects' toolchain pins.
#
# Usage: bash scripts/test_iut_crossrepo.sh _deps/iut

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
iut_rel="${1:-_deps/iut}"
iut="$(realpath "$root/$iut_rel")"
expected_lana="553076af459e7a401bfee63a4607814d1c854477"
actual_lana="$(git -C "$iut" rev-parse HEAD)"
test "$actual_lana" = "$expected_lana" || {
  echo "LANA ref mismatch: expected $expected_lana, got $actual_lana" >&2
  exit 1
}

test "$(tr -d '\n' < "$iut/lean-toolchain")" = 'leanprover/lean4:v4.32.0' || {
  echo "LANA toolchain changed; stop rather than silently repin" >&2
  exit 1
}

python3 - "$root" <<'PY'
import hashlib, json, pathlib, sys
root = pathlib.Path(sys.argv[1])
path = "linear_input/lean_check/PilotVolumeTransport.inc"
manifest = json.loads((root/"docs/integration/manifest.json").read_text("utf-8"))
rows = [r for r in manifest["files"] if r["path"] == path]
assert len(rows) == 1, "missing or duplicate source provenance"
actual = hashlib.sha256((root/path).read_bytes()).hexdigest()
assert actual == rows[0]["sha256"], f"source SHA256 mismatch: {actual}"
print(f"Primitive supplement source verified: {path} SHA256 {actual}")
PY

# The primitive-lean sources are .inc fragments of a monolithic verified Lean
# unit.  For this strictly scoped compatibility check, compile the original
# fragment byte-for-byte in LANA's pinned Lean and Mathlib environment.
test_file="$iut/IutPrimitiveCrossRepo.lean"
{
  printf '%s\n' 'import Mathlib' 'import Iut.WallEquiv.Basic' ''
  cat "$root/linear_input/lean_check/PilotVolumeTransport.inc"
  printf '\n'
  cat "$root/probes/IutPilotCrossRepo.lean"
} > "$test_file"

mkdir -p "$root/verification"
(cd "$iut" && lake build Iut.WallEquiv.Basic)
(cd "$iut" && lake env lean --trust=0 IutPrimitiveCrossRepo.lean) \
  | tee "$root/verification/iut-crossrepo-lean.log"

echo "SUCCESS: imported LANA theorem types + byte-identical primitive-lean supplement compiled together."
