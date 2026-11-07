#!/usr/bin/env bash
# Rebuild the kernel dependency report from the verified assembly.
# Requires: the pinned Lean toolchain and Mathlib cache in lean/, and a prior
# successful `python -B -X utf8 tools/verify.py --integration-only` (which
# writes linear_input/lean_check/MainResult.lean and verification/main-result.json).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
WORK="${DEPS_WORK:-$ROOT/lean/.lake/deps}"  # ignored via .gitignore (.lake/)
OUT="${DEPS_OUT:-$ROOT/docs/dependency}"
LEDGER_REF="${LEDGER_REF:-origin/autonomy/verified-operator-growth}"
mkdir -p "$WORK"
cd "$ROOT"
test -s linear_input/lean_check/MainResult.lean
python3 - <<'PY'
import json; r = json.load(open("verification/main-result.json")); assert r["passed"] is True
PY
cp linear_input/lean_check/MainResult.lean "$WORK/PrimitiveMain.lean"

# Generated autonomy sources, checked against the growth ledger.
if git cat-file -e "$LEDGER_REF:docs/autonomy/ledger.json" 2>/dev/null; then
  git show "$LEDGER_REF:docs/autonomy/ledger.json" > "$WORK/ledger.json"
else
  echo '{"schema_version":1,"cycles":[]}' > "$WORK/ledger.json"
fi
python3 - "$WORK" <<'PY'
import hashlib, json, sys
sys.path.insert(0, "tools/autonomy")
import grow
work = sys.argv[1]
ledger = json.load(open(work + "/ledger.json"))
parts = ["import PrimitiveMain\n"]
for c in ledger["cycles"]:
    src = grow.proof_source(c["cycle"], c["model"])
    if hashlib.sha256(src.encode()).hexdigest() != c["sha256"]:
        raise SystemExit("generated source differs from ledger at cycle %d" % c["cycle"])
    parts.append(src)
open(work + "/AutonomyProbe.lean", "w").write("\n".join(parts))
PY

cd lean
lake env lean --root="$WORK" -o "$WORK/PrimitiveMain.olean" "$WORK/PrimitiveMain.lean" > "$WORK/compile.log"
lake env sh -c "LEAN_PATH=\$LEAN_PATH:$WORK lean --root=$WORK -o $WORK/AutonomyProbe.olean $WORK/AutonomyProbe.lean"
lake env sh -c "LEAN_PATH=\$LEAN_PATH:$WORK lean --run ../tools/deps/ExtractDeps.lean $WORK/raw.json AutonomyProbe -- Elastica PrimitiveMain AutonomyProbe"
cd "$ROOT"
python3 tools/deps/analyze.py --raw "$WORK/raw.json" --assembled "$WORK/PrimitiveMain.lean" \
  --autonomy-ledger "$WORK/ledger.json" --out "$WORK/deps.json"
python3 tools/deps/validate.py --deps "$WORK/deps.json" --assembled "$WORK/PrimitiveMain.lean" --out "$WORK/validation.json"
python3 - "$WORK/validation.json" <<'PY'
import json, sys
v = json.load(open(sys.argv[1]))
assert v["report_declarations"]["mismatched"] == 0, "layer/source mismatch"
assert v["known_edges_main_result"]["equal"], "known proof edges not recovered"
PY
python3 tools/deps/summarize.py --deps "$WORK/deps.json" --validation "$WORK/validation.json" \
  --outdir "$OUT" --commit "$(git rev-parse HEAD)"
