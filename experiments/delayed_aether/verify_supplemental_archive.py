"""Verify supplemental loose files and preview variants retained beside 30 original ZIPs."""
from pathlib import Path, PurePosixPath
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parent / "original_archives" / "supplemental"

def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def main():
    m = json.loads((ROOT / "manifest.json").read_text(encoding="utf-8"))
    assert len(m["members"]) == 18
    src = ROOT / m["zip"]
    raw = src.read_bytes()
    assert len(raw) == m["bytes"] == 549016
    assert sha256(raw) == m["sha256"]
    with zipfile.ZipFile(src) as z:
        assert z.testzip() is None
        items = [x for x in z.infolist() if not x.is_dir()]
        assert [x.filename for x in items] == [x["archive_path"] for x in m["members"]]
        assert len({x.filename for x in items}) == 18
        for info, check in zip(items, m["members"]):
            p = PurePosixPath(info.filename)
            assert not p.is_absolute() and ".." not in p.parts
            assert chr(92) not in info.filename
            data = z.read(info)
            assert len(data) == check["bytes"]
            assert sha256(data) == check["sha256"]
    print(json.dumps({
        "status": "PASS", "supplemental_files_sha256_verified": 18,
        "supplemental_archive_bytes": len(raw),
        "purpose": "preserve loose stage outputs and preview variants"
    }, sort_keys=True))

if __name__ == "__main__":
    main()
