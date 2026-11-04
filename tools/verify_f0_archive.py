"""Rerun the supplied F0 finite checks on a disposable copy; preserve the source bytes."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "sources/f0_math_chat_2026-10-29"
INVENTORY = ROOT / "sources/f0_archive_inventory_2026-10-29.json"
OUT = ROOT / "verification"
GENERATED = (
    "02_partitions_and_chains.md",
    "data/idempotents_by_rank.csv",
    "data/merge_edges_N07.csv",
    "data/merge_edges_N08.csv",
    "data/partition_counts_N01_to_N12.csv",
    "data/verification.json",
)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_members(inventory):
    for member in inventory["members"]:
        path = (SOURCE / member["path"]).resolve()
        if not path.is_relative_to(SOURCE.resolve()):
            raise ValueError("Source member outside the retained archive directory")
        if sha(path) != member["sha256"] or path.stat().st_size != member["bytes"]:
            raise ValueError("Source member mismatch: " + member["path"])


def main():
    OUT.mkdir(exist_ok=True)
    inventory = json.loads(INVENTORY.read_text("utf-8"))
    report = dict(timestamp_utc=datetime.now(timezone.utc).isoformat(), passed=False,
                  source_directory=SOURCE.relative_to(ROOT).as_posix(),
                  archive_sha256=inventory["archive_sha256"],
                  verification_script_sha256=sha(SOURCE / "verify.py"),
                  runner_sha256=sha(Path(__file__)), normalized_newlines=True,
                  generated_outputs=[], errors=[])
    started = time.monotonic()
    try:
        check_members(inventory)
        report["source_members_checked"] = len(inventory["members"])
        with tempfile.TemporaryDirectory(prefix="primitive-f0-") as temporary:
            copied = Path(temporary) / "source"
            shutil.copytree(SOURCE, copied)
            command = [sys.executable, "-B", "-X", "utf8", "verify.py"]
            proc = subprocess.run(command, cwd=copied, capture_output=True,
                                  text=True, encoding="utf-8", errors="replace")
            report.update(command=command, exit_code=proc.returncode)
            (OUT / "f0-archive.log").write_text(proc.stdout + proc.stderr, "utf-8")
            if proc.returncode:
                raise ValueError("Supplied finite verifier failed")
            for relative in GENERATED:
                original = (SOURCE / relative).read_bytes()
                fresh = (copied / relative).read_bytes()
                equal = original.replace(b"\r\n", b"\n") == fresh.replace(b"\r\n", b"\n")
                report["generated_outputs"].append(dict(path=relative, match=equal,
                    source_sha256=hashlib.sha256(original).hexdigest(),
                    fresh_sha256=hashlib.sha256(fresh).hexdigest()))
                if not equal:
                    raise ValueError("Generated output mismatch: " + relative)
            report["finite_results"] = json.loads((copied / "data/verification.json").read_text("utf-8"))
        check_members(inventory)
        report["source_preserved"] = True
        report["passed"] = True
    except Exception as exc:
        report["errors"].append(str(exc))
    report["seconds"] = round(time.monotonic() - started, 3)
    report["scope"] = (
        "Finite checks from the supplied archive, rerun without editing that archive. "
        "The embedded lean_verification_performed=false belongs to the supplied Python "
        "verifier; new Lean results are recorded separately by tools/verify.py --proof-only."
    )
    (OUT / "f0-archive.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", "utf-8")
    print(json.dumps({key: report.get(key) for key in
                     ("passed", "exit_code", "seconds", "source_members_checked", "source_preserved", "errors")},
                     ensure_ascii=False))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
