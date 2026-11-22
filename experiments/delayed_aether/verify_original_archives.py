"""Reproducible byte-integrity audit of the 30 original delayed-aether ZIPs.

This validates historical source bytes, NOT any physical prediction.
"""
from pathlib import Path, PurePosixPath
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parent / "original_archives"


def sha256(blob: bytes) -> str:
    return hashlib.sha256(blob).hexdigest()


def main():
    records = json.loads((ROOT / "manifest.json").read_text(encoding="utf8"))["archives"]
    assert [r["stage"] for r in records] == list(range(1, 31))
    expected_paths = set()
    total_files = total_zip_bytes = total_member_bytes = 0

    for record in records:
        stage = record["stage"]
        name = record["zip"]
        assert Path(name).name == name and name.endswith(".zip")
        archive_path = ROOT / f"stage_{stage:02d}" / name
        expected_paths.add(archive_path.resolve())
        raw = archive_path.read_bytes()
        assert len(raw) == record["bytes"]
        assert sha256(raw) == record["sha256"], f"Archive hash mismatch: {stage}"
        total_zip_bytes += len(raw)

        with zipfile.ZipFile(archive_path) as src:
            assert src.testzip() is None, f"ZIP CRC failure: {stage}"
            members = [x for x in src.infolist() if not x.is_dir()]
            assert len(members) == len(record["members"]), f"Member count: {stage}"
            assert [x.filename for x in members] == [x["path"] for x in record["members"]]
            assert len({x.filename for x in members}) == len(members)
            for info, expected in zip(members, record["members"]):
                path = PurePosixPath(info.filename)
                assert not path.is_absolute()
                assert ".." not in path.parts and chr(92) not in info.filename
                content = src.read(info)
                assert len(content) == expected["bytes"]
                assert sha256(content) == expected["sha256"], f"Member hash: {stage}/{info.filename}"
                assert f"{info.CRC:08x}" == expected["crc32"]
                total_files += 1
                total_member_bytes += len(content)

        if stage == 18:
            assert "ether_eighteenth/verify_v18.py" in [x["path"] for x in record["members"]]

    actual_paths = {p.resolve() for p in ROOT.glob("stage_*/*.zip")}
    assert expected_paths == actual_paths, "Missing or extra ZIP archive"
    assert len(expected_paths) == 30 and total_files == 623
    assert total_zip_bytes == 13238705 and total_member_bytes < 100_000_000
    print(json.dumps({
        "status": "PASS", "archives": len(expected_paths),
        "members_sha256_verified": total_files,
        "total_original_zip_bytes": total_zip_bytes,
        "total_unpacked_bytes": total_member_bytes,
        "stage_18_verify_script_inside_original_zip": True,
        "scope": "byte fidelity only; gravity derivation unproved"
    }, sort_keys=True))


if __name__ == "__main__":
    main()
