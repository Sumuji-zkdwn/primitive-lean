"""Compile the pinned Möbius package and audit every theorem in its four proof modules."""
import json

from verify_toolchain_modules import ROOT, digest, run


PACKAGE = "experiments/mobius_430"


def main():
    package = ROOT / PACKAGE
    ledger = json.loads((package / "source-provenance.json").read_bytes())
    actual = {p.relative_to(package).as_posix(): digest(p) for p in (package / "Research").glob("*.lean")}
    if actual != ledger["source_sha256"]:
        raise ValueError("The preserved Möbius sources differ from their provenance ledger")
    for name, expected in ledger["package_sha256"].items():
        if digest(package / name) != expected:
            raise ValueError("Möbius package pin mismatch: " + name)
    vendor = actual["Research/EComplexThirdParty.lean"]
    # This exact upstream file uses unsafe for its two display helpers only.
    findings = {vendor: {"source_terms": ["unsafe"], "warnings": ledger["vendor_warnings"]}}
    report = run(package=PACKAGE, output="mobius-430", findings=findings)
    if not report["passed"]:
        return 1
    # The old curated audit is a fifth module containing only #print axioms.
    audit = next(item for item in report["modules"] if item["module"] == "Research.MobiusProjectiveAudit")
    log = (ROOT / audit["log"]).read_text(encoding="utf-8")
    selected = [line.split()[-1] for line in (package / "Research/MobiusProjectiveAudit.lean")
                .read_text(encoding="utf-8").splitlines() if line.startswith("#print axioms ")]
    audited = {row["name"] for row in report["axioms"]}
    if not selected or any(("'" + name + "'") not in log or name not in audited for name in selected):
        raise ValueError("A selected theorem is missing from the original audit or the full environment audit")
    print(f"Verified {len(selected)} selected theorems against {len(audited)} complete environment records")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
