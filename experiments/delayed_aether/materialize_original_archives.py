"""Materialize all immutable delayed-aether ZIP members as individual Git files.

Stage archives remain authoritative; this script only extracts/checks exact bytes.
No experiments or physical claims are rerun. No network access is needed.
"""
from __future__ import annotations
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import sys
import zipfile

BASE = Path(__file__).resolve().parent
SRC = BASE / "original_archives"
OUT = BASE / "original_extracted"


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def safe_path(value: str) -> Path:
    path = PurePosixPath(value)
    assert not path.is_absolute() and ".." not in path.parts, value
    assert chr(92) not in value and ".git" not in path.parts, value
    return Path(*path.parts)


def iterate():
    meta = json.loads((SRC / "manifest.json").read_text(encoding="utf-8"))
    assert [x["stage"] for x in meta["archives"]] == list(range(1, 31))
    for rec in meta["archives"]:
        stage = rec["stage"]
        source_path = SRC / f"stage_{stage:02d}" / rec["zip"]
        assert sha(source_path.read_bytes()) == rec["sha256"], source_path
        with zipfile.ZipFile(source_path) as z:
            members = [x for x in z.infolist() if not x.is_dir()]
            assert [x.filename for x in members] == [m["path"] for m in rec["members"]]
            for item, member in zip(members, rec["members"]):
                content = z.read(item)
                assert len(content) == member["bytes"]
                assert sha(content) == member["sha256"], (stage, item.filename)
                yield Path(f"stage_{stage:02d}") / safe_path(item.filename), content, member["sha256"]

    suppl = json.loads((SRC / "supplemental" / "manifest.json").read_text(encoding="utf-8"))
    zipfile_path = SRC / "supplemental" / suppl["zip"]
    assert sha(zipfile_path.read_bytes()) == suppl["sha256"]
    with zipfile.ZipFile(zipfile_path) as z:
        members = [x for x in z.infolist() if not x.is_dir()]
        assert [x.filename for x in members] == [m["archive_path"] for m in suppl["members"]]
        for item, member in zip(members, suppl["members"]):
            content = z.read(item)
            assert len(content) == member["bytes"] and sha(content) == member["sha256"]
            yield Path("supplemental") / safe_path(item.filename), content, member["sha256"]


def main():
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write", action="store_true",
                       help="write individual member files into original_extracted")
    group.add_argument("--check", action="store_true",
                       help="verify previously extracted member bytes against source ZIPs")
    args = parser.parse_args()
    count = 0
    total_bytes = 0
    expected = set()
    for rel, content, expected_hash in iterate():
        destination = OUT / rel
        assert destination not in expected, ("Duplicate output", destination)
        expected.add(destination)
        if args.write:
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(content)
        else:
            assert destination.is_file(), ("Missing extracted file", destination)
            assert sha(destination.read_bytes()) == expected_hash, destination
        count += 1
        total_bytes += len(content)

    assert count == 641
    if args.check:
        actual = {p for p in OUT.rglob("*") if p.is_file() and p != OUT / "README.md"}
        assert actual == expected, {
            "missing": [str(x) for x in sorted(expected - actual)[:10]],
            "unexpected": [str(x) for x in sorted(actual - expected)[:10]],
        }
    print(json.dumps({
        "status": "PASS",
        "mode": "write" if args.write else "check",
        "files": count,
        "bytes": total_bytes,
        "source_stage_zip_files": 623,
        "additional_variants": 18
    }, sort_keys=True))


if __name__ == "__main__":
    main()
