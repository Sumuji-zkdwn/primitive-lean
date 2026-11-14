"""Fresh source compilation and theorem-axiom audit of standalone Lean modules.

The Elastica Lake library is a prerequisite and is checked by the main verifier.
This adds coverage for every tracked lean/*.lean and lean/Research/*.lean module
outside that library. It does not replace the joint linear-input proof checker.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def imports_in(code):
    imports = []
    for line in code.splitlines():
        match = re.fullmatch(r"\s*(?:(?:public|private|meta)\s+)*import\s+(.+?)\s*", line)
        if match:
            names = match.group(1).split()
            if not all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", name) for name in names):
                raise ValueError("Unsupported import syntax: " + line.strip())
            imports.extend(names)
        elif re.search(r"\bimport\b", line):
            raise ValueError("Unsupported import syntax: " + line.strip())
    return imports


def inventory(root):
    from verify import strip_comments_strings
    tracked = subprocess.check_output(
        ["git", "ls-files", "-z", "lean"], cwd=root).decode("utf-8").split("\0")
    modules = {}
    for relative in tracked:
        path = Path(relative)
        if path.suffix != ".lean":
            continue
        name = ".".join(path.relative_to("lean").with_suffix("").parts)
        code = strip_comments_strings((root / path).read_text(encoding="utf-8"))
        modules[name] = {
            "path": relative,
            "sha256": digest(root / path),
            "imports": imports_in(code),
            "explicit_theorems": len(re.findall(r"\b(?:theorem|lemma)\s+", code)),
            "forbidden": sorted(set(re.findall(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code))),
        }
    return modules


def run(root=ROOT, selected=None):
    root = Path(root).resolve()
    lean = root / "lean"
    modules = inventory(root)
    standalone = {name for name in modules if name != "Elastica" and not name.startswith("Elastica.")}
    # Audit.lean only repeats the main library's explicit audits.
    standalone.discard("Audit")
    wanted = set(standalone if not selected else selected)
    if not wanted <= standalone:
        raise ValueError("Unknown standalone modules: " + repr(sorted(wanted - standalone)))
    ordered, visiting = [], set()

    def visit(name):
        if name in ordered:
            return
        if name in visiting:
            raise ValueError("Cyclic local imports: " + name)
        visiting.add(name)
        for dependency in modules[name]["imports"]:
            if dependency in standalone:
                visit(dependency)
        visiting.remove(name)
        ordered.append(name)

    for name in sorted(wanted):
        visit(name)
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    out = root / "verification/toolchain-modules" / stamp
    out.mkdir(parents=True)
    report = {
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "source_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip(),
        "dirty": bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=root, text=True).strip()),
        "scope": "Fresh standalone-module source compilation and all imported local theorem axiom audit; Elastica prerequisite and joint assembly checked separately",
        "passed": False, "complete_standalone_inventory": set(ordered) == standalone,
        "toolchain": (lean / "lean-toolchain").read_text().strip(),
        "manifest_sha256": digest(lean / "lake-manifest.json"),
        "explicit_source_theorems": sum(modules[name]["explicit_theorems"] for name in ordered),
        "inventory": {name: modules[name] for name in ordered}, "modules": [],
        "axioms": [], "errors": [],
    }
    def save():
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        pointer = "latest.json" if report["complete_standalone_inventory"] else "latest-partial.json"
        (out.parent / pointer).write_text(json.dumps({"report": (out / "report.json").relative_to(root).as_posix(), "passed": report["passed"], "complete_standalone_inventory": report["complete_standalone_inventory"]}, indent=2) + "\n", encoding="utf-8")

    report["stage"] = "environment_resolution"
    save()
    # Resolve the same Lake environment once. Subsequent checks use its actual
    # Lean executable directly; no ambient credentials are printed or recorded.
    environment_keys = ("PATH", "LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "LD_LIBRARY_PATH", "DYLD_LIBRARY_PATH")
    bootstrap = subprocess.run(
        ["lake", "env", sys.executable, "-c",
         "import json,os; print(json.dumps({k:os.environ[k] for k in " + repr(environment_keys) + " if k in os.environ}))"],
        cwd=lean, capture_output=True, text=True, encoding="utf-8")
    if bootstrap.returncode:
        report["errors"].append("Lake environment resolution failed: " + bootstrap.stderr)
        save()
        return report
    resolved = json.loads(bootstrap.stdout)
    environment = {**os.environ, **resolved}
    lean_binary = shutil.which("lean", path=resolved["PATH"])
    if not lean_binary:
        report["errors"].append("Lake environment has no Lean executable")
        save()
        return report
    version = subprocess.check_output([lean_binary, "--version"], cwd=lean, env=environment, text=True).strip()
    if "version " + report["toolchain"].rsplit(":v", 1)[-1] not in version:
        report["errors"].append("Lean binary disagrees with the toolchain pin: " + version)
        save()
        return report
    report.update(lean_executable=lean_binary, lean_version=version,
                  lean_path=resolved.get("LEAN_PATH", ""), environment_resolution="lake env; explicit non-secret path variables only")

    def command(args, label):
        started = time.monotonic()
        result = subprocess.run(args, cwd=lean, env=environment, text=True, encoding="utf-8", errors="replace", capture_output=True)
        text = result.stdout + result.stderr
        log = out / (label + ".log")
        log.write_text(text, encoding="utf-8")
        return {"command": args, "exit_code": result.returncode, "seconds": round(time.monotonic() - started, 3),
                "log": log.relative_to(root).as_posix(),
                "warnings": [line for line in text.splitlines() if "warning:" in line]}, text

    report["stage"] = "compilation"
    save()
    failed = set()
    for name in ordered:
        row = modules[name]
        if row["forbidden"]:
            report["errors"].append(f"{name}: forbidden source terms {row['forbidden']}")
            failed.add(name)
            continue
        broken = set(row["imports"]) & failed
        if broken:
            report["errors"].append(f"{name}: failed dependencies {sorted(broken)}")
            failed.add(name)
            continue
        target = lean / ".lake/build/lib/lean" / (name.replace(".", "/") + ".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        print("Checking " + name, flush=True)
        result, text = command([lean_binary, "--trust=0", "-o", str(target),
                               str(Path(row["path"]).relative_to("lean"))], name)
        report["modules"].append({"module": name, **result})
        if result["exit_code"] or result["warnings"]:
            failed.add(name)
            report["errors"].append(name + ": source compilation failed or emitted warnings")
            print(text, flush=True)
        save()
    if not failed:
        quoted = ", ".join("`" + name for name in ordered)
        audit = out / "Audit.lean"
        audit.write_text("\n".join("import " + name for name in ordered) + "\nimport Lean.Util.CollectAxioms\n" +
            "open Lean Elab Command\nrun_cmd do\n" +
            f"  let owned : Array Name := #[{quoted}]\n" +
            "  let env ← getEnv\n  for (name, info) in env.constants.toList do\n" +
            "    if let some idx := env.getModuleIdxFor? name then\n" +
            "      let owner := env.header.moduleNames[idx.toNat]!\n" +
            "      if owned.contains owner && info.isTheorem then\n" +
            "        let axioms ← collectAxioms name\n" +
            '        let record := Json.mkObj [("module", toJson owner.toString), ("name", toJson name.toString), ("axioms", toJson (axioms.map Name.toString))]\n' +
            '        liftIO <| IO.println ("MODULE_AXIOM " ++ record.compress)\n', encoding="utf-8")
        result, text = command([lean_binary, "--trust=0", str(audit)], "axioms")
        report["audit"] = result
        if result["exit_code"] or result["warnings"]:
            report["errors"].append("Generated theorem audit failed")
            print(text, flush=True)
        else:
            records = [json.loads(line.removeprefix("MODULE_AXIOM ")) for line in text.splitlines() if line.startswith("MODULE_AXIOM ")]
            report["axioms"] = records
            names = [row["name"] for row in records]
            if len(names) != len(set(names)):
                report["errors"].append("Duplicate theorem audit record")
            for name in ordered:
                count = sum(row["module"] == name for row in records)
                if count < modules[name]["explicit_theorems"]:
                    report["errors"].append(f"{name}: theorem audit coverage {count} below explicit count {modules[name]['explicit_theorems']}")
            for row in records:
                if not set(row["axioms"]) <= ALLOWED:
                    report["errors"].append(f"{row['name']}: unexpected axioms {row['axioms']}")
    for name in ordered:
        if digest(root / modules[name]["path"]) != modules[name]["sha256"]:
            report["errors"].append(name + ": source changed during verification")
    if digest(lean / "lake-manifest.json") != report["manifest_sha256"]:
        report["errors"].append("Dependency manifest changed during verification")
    if (lean / "lean-toolchain").read_text().strip() != report["toolchain"]:
        report["errors"].append("Toolchain pin changed during verification")
    report["passed"] = not report["errors"]
    report["audited_theorem_declarations_including_generated"] = len(report["axioms"])
    report["stage"] = "completed"
    save()
    print(json.dumps({"passed": report["passed"], "modules": len(report["modules"]), "theorems": len(report["axioms"]), "errors": report["errors"], "report": str(out / "report.json")}, indent=2), flush=True)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--module", action="append", help="Check this module and its local prerequisites; omit for all standalone modules")
    args = parser.parse_args()
    return 0 if run(selected=args.module)["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
