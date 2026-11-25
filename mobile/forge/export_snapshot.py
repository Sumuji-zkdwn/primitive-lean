"""Only export a snapshot after the original Forge's real Lean replay."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.autonomy import forge_lean_evolution as evo

def main():
    p = argparse.ArgumentParser()
    for name in ("state", "semantic", "head", "day", "state-sha", "semantic-sha", "evidence"):
        p.add_argument("--" + name, required=True)
    a = p.parse_args()
    state, semantic, tables, count = evo.prepare_cycle(
        Path(a.state), Path(a.semantic), a.day, a.head, Path(a.evidence))
    snapshot = {
        "schema": 1, "control_sha": a.head, "evolution_sha": a.state_sha,
        "semantic_sha": a.semantic_sha, "verification": "ORIGINAL_LEAN_REPLAY",
        "generation_count": count, "evolution": state, "semantic": semantic,
        "tables": [[k, list(v), hashlib.sha256(bytes(v)).hexdigest()] for k, v in tables.items()],
    }
    app = Path(__file__).resolve().parent / "app/src/main"
    assets = app / "assets"
    assets.mkdir(parents=True, exist_ok=True)
    (assets / "forge-snapshot.json").write_text(
        json.dumps(snapshot, ensure_ascii=False, separators=(",", ":")), encoding="utf-8")
    target = app / "python/tools/autonomy"
    target.mkdir(parents=True, exist_ok=True)
    (target.parent / "__init__.py").touch()
    (target / "__init__.py").touch()
    for name in ("forge_lean_evolution", "forge_lean_group", "forge_lean_certificate",
                 "forge_lean_feedback", "forge_lean_reentry", "generic_forge", "semantic_forge"):
        shutil.copyfile(ROOT / "tools/autonomy" / (name + ".py"), target / (name + ".py"))
    print("exported", count, "original generations and", len(tables), "tables")

if __name__ == "__main__":
    main()
