"""Host-side tests against the actual copied Forge and actual verified snapshot."""
from pathlib import Path
import json
import tempfile
import sys

APP = Path(__file__).resolve().parent / "app/src/main"
sys.path.insert(0, str(APP / "python"))
from mobile_forge import Engine, STATUS

def main():
    snapshot = (APP / "assets/forge-snapshot.json").read_text(encoding="utf-8")
    with tempfile.TemporaryDirectory() as tmp:
        a, b = (Engine(Path(tmp) / n, snapshot) for n in ("a.json", "b.json"))
        for text in ("こんにちは", "これは何ですか？", "こんにちは", "別の応答を。", "AB", "λ"):
            assert a.send(text) == b.send(text)
        assert a.view()["turn_count"] == 6 and a.view()["local"] > 0
        assert a.state["scores"] and len(a.state["alphabet"]) > 1
        reopened = Engine(a.path, snapshot)
        assert reopened.export() == a.export()
        assert reopened.send("続き") == a.send("続き")
        report = json.loads(a.export())
        assert all(r["status"] == STATUS for r in report["experiment"]["locals"])
        assert report["snapshot"]["evolution"] == json.loads(snapshot)["evolution"]
        damaged = json.loads(b.path.read_text())
        damaged["locals"][0]["behavior_sha256"] = "0" * 64
        b.path.write_text(json.dumps(damaged))
        try:
            Engine(b.path, snapshot)
        except ValueError:
            pass
        else:
            raise AssertionError("tampered local table accepted")
    print("PASS deterministic chat, next-input feedback, local reentry, reload, tamper rejection")

if __name__ == "__main__":
    main()
    from test_finite_reason import test
    test()

