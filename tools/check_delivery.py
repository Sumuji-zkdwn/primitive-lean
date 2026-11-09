"""Validate the unified reader, canonical sources, and preserved provenance.

Read-only toward Research. Browser records retain their original hashes and
are reported as historical when the current HTML differs. This script does
not rerun Lean or a browser; tools/verify.py orchestrates the whole delivery.
"""
from pathlib import Path
from datetime import datetime, timezone
from collections import Counter
from html.parser import HTMLParser
from urllib.parse import unquote, urlsplit
import hashlib
import json
import re
import zipfile

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "verification"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path):
    return json.loads(path.read_text("utf-8"))


class Page(HTMLParser):
    def __init__(self):
        super().__init__()
        self.links, self.ids, self.duplicates = [], set(), []
        self.math = 0

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if "id" in attrs:
            if attrs["id"] in self.ids:
                self.duplicates.append(attrs["id"])
            self.ids.add(attrs["id"])
        self.links.extend((tag, attrs[key]) for key in ("href", "src") if key in attrs)
        if tag == "math":
            self.math += 1


def parse(path):
    page = Page()
    page.feed(path.read_text("utf-8"))
    return page


def mathematical_blocks(text):
    matches = re.findall(r"\\\[(.*?)\\\]|\\\((.*?)\\\)", text, re.S)
    return Counter(re.sub(r"\s+", "", re.sub(r"\\tag\{[^}]*\}", "", a or b))
                   for a, b in matches)


def main():
    errors, pages, sources, browser_records = [], [], [], []
    before = read_json(OUT / "before-unification.json")
    archive_path = ROOT / before["archive"]
    if sha(archive_path) != before["archive_sha256"]:
        errors.append("Pre-unification archive hash differs")
    proof_files = []
    with zipfile.ZipFile(archive_path) as archive:
        if archive.testzip() is not None:
            errors.append("Archive integrity test failed")
        for rel, digest in before["files"].items():
            if hashlib.sha256(archive.read(rel)).hexdigest() != digest:
                errors.append("Archived source differs: " + rel)
        old_report = json.loads(archive.read("linear_input/lean_results.json"))
        proof_files = sorted({(ROOT / "linear_input" / d["file"]).resolve().relative_to(ROOT).as_posix()
            for d in old_report["parent_declarations"] + old_report["declarations"]})
        for rel in proof_files + ["lean/Elastica.lean", "lean/Audit.lean", "lean/lakefile.toml",
                                 "lean/lean-toolchain", "lean/lake-manifest.json", "linear_input/verify_lean.py"]:
            if (ROOT / rel).read_bytes() != archive.read(rel):
                errors.append("Retained proof source or configuration changed: " + rel)

        old_math = mathematical_blocks(archive.read("原始の形式化.md").decode("utf-8"))
        old_math.update(mathematical_blocks(archive.read("linear_input/線形入力の使い方.md").decode("utf-8")))
        new_math = mathematical_blocks((ROOT / "原始の形式化.md").read_text("utf-8"))
        missing_math = old_math - new_math
        if missing_math:
            errors.append("Original mathematical blocks missing from unified reader")

        provenance = read_json(ROOT / "sources/provenance.json")["research"]
        records = [dict(path=r["source"], sha256=r["source_sha256"],
                        excerpt=r["excerpt"], excerpt_sha256=r["excerpt_sha256"])
                   for r in provenance]
        records += [dict(r, excerpt="linear_input/" + r["excerpt"])
                    for r in read_json(ROOT / "linear_input/sources.json")["local_sources"]]
        for row in records:
            src = Path(row["path"])
            available = src.is_file()
            entry = dict(source=str(src), available=available,
                         unchanged=sha(src) == row["sha256"] if available else None,
                         excerpt=row["excerpt"],
                         excerpt_unchanged=sha(ROOT / row["excerpt"]) == row["excerpt_sha256"])
            if not available and src.is_relative_to(ROOT):
                rel = src.relative_to(ROOT).as_posix()
                errors.append("Missing local provenance source: " + rel)
            if entry["unchanged"] is False or not entry["excerpt_unchanged"]:
                errors.append("Source or excerpt changed: " + row["path"])
            sources.append(entry)

        for record_path, base in ((OUT / "browser.json", ROOT),
                                  (ROOT / "linear_input/qa/browser.json", ROOT / "linear_input")):
            record = read_json(record_path)
            hashes = record.get("source_hashes", record.get("reviewed_html_sha256", {}))
            for rel, digest in hashes.items():
                current = base / rel
                archive_rel = current.relative_to(ROOT).as_posix()
                if archive_rel.startswith("linear_input/") and sha(current) != digest:
                    archive_rel = "linear_input/lean_check/before/" + Path(rel).name
                archived_match = hashlib.sha256(archive.read(archive_rel)).hexdigest() == digest
                if not archived_match:
                    errors.append("Historical browser source not preserved: " + rel)
                browser_records.append(dict(record=record_path.relative_to(ROOT).as_posix(),
                    file=current.relative_to(ROOT).as_posix(),
                    current_file_matches_review=sha(current) == digest,
                    historical_review_source_preserved=archived_match,
                    archived_file=archive_rel))
            for rel in record.get("screenshots", []):
                if not (base / rel).is_file():
                    errors.append("Missing historical screenshot: " + rel)
                elif sha(base / rel) != before["files"][(base / rel).relative_to(ROOT).as_posix()]:
                    errors.append("Historical screenshot changed: " + rel)

    html_files = [*ROOT.glob("*.html"), *(ROOT / "linear_input").glob("*.html")]
    parsed = {path.resolve(): parse(path) for path in html_files}
    for path in html_files:
        raw, page = path.read_text("utf-8"), parsed[path.resolve()]
        rel = path.relative_to(ROOT).as_posix()
        if any(token in raw for token in ("MATHPLACEHOLDER", "katex-error", "\ufffd")):
            errors.append("Malformed rendering: " + rel)
        if page.duplicates:
            errors.append("Duplicate anchors: " + rel)
        local_links = 0
        for tag, url in page.links:
            parts = urlsplit(url)
            if parts.scheme or parts.netloc:
                if tag in ("script", "img", "link", "iframe"):
                    errors.append("External runtime resource: " + rel + ": " + url)
                continue
            dest = (path.parent / unquote(parts.path)).resolve() if parts.path else path.resolve()
            if not dest.is_file():
                errors.append("Missing link: " + rel + ": " + url)
            elif parts.fragment and dest.suffix == ".html":
                target_page = parsed.get(dest) or parse(dest)
                if unquote(parts.fragment) not in target_page.ids:
                    errors.append("Missing target anchor: " + rel + ": " + url)
            local_links += 1
        pages.append(dict(file=rel, math_expressions=page.math, checked_local_references=local_links))
    rendered = read_json(OUT / "render.json")
    for row in rendered:
        if next(p["math_expressions"] for p in pages if p["file"] == row["file"]) != row["math_expressions"]:
            errors.append("Render count differs: " + row["file"])
    css = ROOT / "vendor/katex/katex.min.css"
    fonts = re.findall(r"url\(([^)]+)\)", css.read_text("utf-8"))
    for font in fonts:
        if not (css.parent / font.strip("'\"")).is_file():
            errors.append("Missing font: " + font)
    lean = read_json(OUT / "lean.json")
    if not lean["passed"]:
        errors.append("Unified Lean verification failed")
    for rel, digest in lean["source_hashes"].items():
        if not (ROOT / rel).is_file() or sha(ROOT / rel) != digest:
            errors.append("Stale Lean verification: " + rel)
    main_result_path = OUT / "main-result.json"
    main_result = read_json(main_result_path) if main_result_path.is_file() else {}
    if not main_result.get("passed"):
        errors.append("Additive main-result verification missing or failed")
    else:
        expected_supplements = [
            ("linear_input/lean_check/MainResult.inc", "LinearInputMainResult"),
            ("linear_input/lean_check/GeneralMinimum.inc", "LinearInputMinimum"),
            ("linear_input/lean_check/SupportComposition.inc", "LinearInputSupportComposition"),
            ("linear_input/lean_check/QuarticClassification.inc", "LinearInputQuarticClassification"),
            ("linear_input/lean_check/CurvatureRigidity.inc", "LinearInputCurvatureRigidity"),
        ]
        expected_sources = [source for source, _ in expected_supplements]
        groups = main_result.get("supplemental_groups", [])
        if (main_result.get("supplemental_sources") != expected_sources
                or [(group.get("source"), group.get("namespace")) for group in groups]
                != expected_supplements):
            errors.append("Supplemental proof sources or namespaces are incomplete")
        grouped_declarations = []
        for group in groups:
            declarations = group.get("declarations", [])
            if (not declarations
                    or group.get("declaration_count") != len(declarations)
                    or group.get("theorem_count") != sum(
                        d["kind"] in ("theorem", "lemma") for d in declarations)
                    or group.get("sha256") != main_result["source_hashes"].get(group.get("source"))
                    or any(d["file"] != group.get("source")
                           or not d["name"].startswith(group.get("namespace", "") + ".")
                           for d in declarations)):
                errors.append("Supplemental declaration group is incomplete: " + str(group.get("source")))
            grouped_declarations.extend(declarations)
        if (grouped_declarations != main_result["declarations"]
                or main_result["declaration_count"] != len(grouped_declarations)
                or main_result["theorem_count"] != sum(
                    d["kind"] in ("theorem", "lemma") for d in grouped_declarations)):
            errors.append("Supplemental declaration groups do not match the combined audit")
        for required in ("linear_input/lean_results.json", "linear_input/lean_check/All.lean",
                         *expected_sources, "linear_input/lean_check/MainResult.lean",
                         "tools/verify_main_result.py", "tools/verify.py", "tools/check_delivery.py"):
            if required not in main_result["source_hashes"]:
                errors.append("Missing main-result source binding: " + required)
        for rel, digest in main_result["source_hashes"].items():
            if not (ROOT / rel).is_file() or sha(ROOT / rel) != digest:
                errors.append("Stale main-result verification: " + rel)
        if (not main_result["joint_axiom_audit"] or not main_result["baseline_axioms_match"]
                or not main_result.get("astra_environment_audit", {}).get("passed", False)
                or main_result["compile"]["exit_code"] != 0
                or main_result["warnings"] or main_result["unexpected"]
                or main_result["forbidden_tokens"] or main_result["changed_during_verification"]
                or not all(row["match"] for row in main_result["dependencies"])
                or not all(row["match"] for row in main_result["dependencies_after_compile"])):
            errors.append("Additive main-result audit is incomplete")
        audit_log = ROOT / main_result["compile"]["log"]
        if not audit_log.is_file() or sha(audit_log) != main_result["log_sha256"]:
            errors.append("Main-result audit log missing or changed")
        if (lean["theorem_count"] != main_result["total_theorem_count"]
                or lean["declaration_count"] != main_result["total_declaration_count"]
                or lean["declarations"] != main_result["all_declarations"]
                or lean["axioms"] != main_result["axioms"]
                or lean.get("added_declarations") != main_result["declarations"]):
            errors.append("Unified and additive Lean audit reports differ")
        if lean["source_hashes"].get("verification/main-result.json") != sha(main_result_path):
            errors.append("Unified overview does not bind the current main-result report")
    mapping = read_json(OUT / "unification-text-map.json")
    if not mapping["preservation_check"]["passed"] or mapping["sha256"] != sha(ROOT / mapping["target"]):
        errors.append("Text correspondence failed or does not match current manuscript")
    if len(proof_files) != 60:
        errors.append("Expected 60 retained proof source files")
    if (ROOT / "lean/Primitive").exists() or (ROOT / "lean/Primitive.lean").exists():
        errors.append("Unrequested merged library source still present")
    for rel in ("verification/examples.json", "verification/scale-response.json",
                "verification/combinations.json", "linear_input/checks.json"):
        if not read_json(ROOT / rel)["passed"]:
            errors.append("Numerical validation failed: " + rel)
    report = dict(passed=not errors, timestamp_utc=datetime.now(timezone.utc).isoformat(),
        errors=errors, pages=pages, local_katex_font_references=len(fonts),
        research_sources=sources, retained_proof_files=len(proof_files),
        proof_sources_and_configuration_byte_identical=not any("Retained proof source" in error for error in errors),
        proof_layout="Elastica and linear-input proof files retain their original locations and contents.",
        supplemental_proof=dict(source="linear_input/lean_check/MainResult.inc",
            sources=main_result.get("supplemental_sources", []),
            groups=main_result.get("supplemental_groups", []),
            report="verification/main-result.json", passed=main_result.get("passed", False),
            theorem_count=main_result.get("theorem_count", 0),
            declaration_count=main_result.get("declaration_count", 0)),
        mathematical_blocks_preserved=dict(previous_occurrences=sum(old_math.values()),
            current_occurrences=sum(new_math.values()), missing_occurrences=sum(missing_math.values())),
        pre_unification_archive=before["archive"], archived_files_verified=len(before["files"]),
        text_migration_report="verification/unification-text-map.json",
        browser_evidence=browser_records,
        current_display_validation="Static local KaTeX rendering, HTML anchors, links and font resources. Browser screenshots are historical only unless their source hash matches the current file.",
        unified_lean_report="verification/lean.json", theorem_count=lean["theorem_count"],
        declaration_count=lean["declaration_count"])
    (OUT / "delivery.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", "utf-8")
    (ROOT / "linear_input/delivery.json").write_text(json.dumps(dict(
        passed=report["passed"], timestamp_utc=report["timestamp_utc"],
        unified_report="../verification/delivery.json", scope="Compatibility pointer to the unified delivery verification."),
        ensure_ascii=False, indent=2) + "\n", "utf-8")
    print(json.dumps({k: v for k, v in report.items() if k not in ("research_sources", "browser_evidence")},
                     ensure_ascii=False, indent=2))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
