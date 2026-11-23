"""Read-only checks for games/dependency-duel/index.html.
Run: python3 games/dependency-duel/verify.py
"""
from functools import lru_cache
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HTML = Path(__file__).with_name("index.html")
SOURCE = ROOT / "docs/dependency/data/deps.json"
MARK = '<script type="application/json" id="dataset">'

def run() -> None:
    html = HTML.read_text(encoding="utf-8")
    data = json.loads(html.split(MARK, 1)[1].split("</script>", 1)[0])
    nodes = data["nodes"]
    assert len(nodes) == 18 and sum(len(n["depends"]) for n in nodes) == 20
    assert [n["id"] for n in nodes] == list(range(18))
    by_name = {n["name"]: n["id"] for n in nodes}
    assert len(by_name) == 18

    raw = SOURCE.read_bytes()
    git_blob = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
    assert git_blob == data["source_blob_sha"], (git_blob, data["source_blob_sha"])
    graph = json.loads(raw)["nodes"]
    for n in nodes:
        record = graph[n["name"]]
        assert record["kind"] == "theorem" and record["source"] == n["source"]
        actual = sorted(by_name[d] for d in record["direct"]["proof"] if d in by_name)
        assert actual == sorted(n["depends"]), n["name"]

    def closure(i: int) -> int:
        removed = 1 << i
        while True:
            later = removed
            for n in nodes:
                if not (removed & 1 << n["id"]) and any(removed & 1 << d for d in n["depends"]):
                    later |= 1 << n["id"]
            if later == removed:
                return removed
            removed = later

    cones = [closure(i) for i in range(18)]
    @lru_cache(None)
    def has_win(mask: int) -> bool:
        if not mask:
            return False
        return any(not has_win(mask & ~cones[i]) for i in range(18) if mask & 1 << i)

    initial = (1 << 18) - 1
    winning_moves = [i for i in range(18) if not has_win(initial & ~cones[i])]
    assert winning_moves == [7], winning_moves
    print("PASS: 18 kernel theorems, 20 proof edges, pinned Git blob SHA")
    print("PASS: unique winning opening #08 gradXu_injective")
    print("Analyzed states:", has_win.cache_info().currsize)

if __name__ == "__main__":
    run()
