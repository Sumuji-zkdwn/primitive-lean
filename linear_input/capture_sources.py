"""Read-only capture of the local passages used by this companion."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
RESEARCH = Path(r"C:\Users\Dalcia\Research\05_Notes")
SPECS = [
    ("energy_findings", RESEARCH / "recent_discussions_2026-10-19/energy_findings.md",
     [(27, 75)], "General quartic family, completing the square, distinction between static and dynamic elimination."),
    ("power_log", RESEARCH / "abstract_elastica_reference_2026-10-19/power_log_bridge_2026-10-20/べき対数とEの簡約.md",
     [(49, 99)], "Original power/log coordinate simplification and its domain."),
    ("primitive_operations", RESEARCH / "primitive_operations_2026-10-20/原始の操作と忘却の導出.md",
     [(133, 183), (308, 308)], "Observation equivalence and the distinction between frozen input and feedback differentiation."),
    ("affine_equivalence", ROOT / "lean/Elastica/AffineEquivalence.lean",
     [(1, 49)], "Existing Lean declarations for affine density changes; source read, no new Lean build."),
]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def capture():
    destination = HERE / "provenance"
    destination.mkdir(exist_ok=True)
    records = []
    for key, path, ranges, usage in SPECS:
        before = path.read_bytes()
        lines = before.decode("utf-8-sig").splitlines()
        chunks = [f"Source: {path}\nSHA256: {sha(before)}\n"]
        for start, end in ranges:
            assert 1 <= start <= end <= len(lines)
            chunks.append(f"\n--- original lines {start}-{end} ---\n")
            chunks.extend(f"{i}: {lines[i-1]}\n" for i in range(start, end + 1))
        excerpt = destination / (key + "_excerpt.txt")
        excerpt.write_text("".join(chunks), encoding="utf-8")
        after = path.read_bytes()
        assert sha(before) == sha(after), "Source changed during capture"
        records.append(dict(
            id=key, path=str(path), sha256=sha(before), line_ranges=ranges,
            excerpt=excerpt.relative_to(HERE).as_posix(),
            excerpt_sha256=sha(excerpt.read_bytes()), use=usage,
            source_unmodified_during_capture=True,
        ))
    record = {
        "captured_utc": datetime.now(timezone.utc).isoformat(),
        "research_policy": "Read-only; passages are copied with original line numbers.",
        "local_sources": records,
        "web_source": {
            "url": "https://github.com/ryantibs/convexopt-book1/blob/main/convex_conjugates.tex",
            "author": "Ryan Tibshirani",
            "access_date_local": "2026-10-20",
            "used_for": "Definition of convex conjugate and double conjugate as greatest closed convex minorant. Specific quartic formulas are derived in the companion.",
            "verified_passages": ["eq:conjugate", "eq:double_conjugate", "eq:double_conjugate_affine_minorant"],
        },
        "derivation_scope": "Inverse design, exact gap certificate and the practical consequences are derived in this companion, not attributed as quotations from Research.",
    }
    (HERE / "sources.json").write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"captured": len(records), "sources_unmodified": True}))


if __name__ == "__main__":
    capture()
