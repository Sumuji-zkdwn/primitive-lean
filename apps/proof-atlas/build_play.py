#!/usr/bin/env python3
"""Build/check a completely self-contained read-only theorem atlas HTML page."""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SCRIPTS = '<script src="./atlas.js"></script>\n<script src="./ui.js"></script>'
TITLE = '<title>PRIMITIVE ATLAS — 証明の地図</title>'
BUNDLED = '<title>PRIMITIVE ATLAS — オフライン版</title>'


def build() -> str:
    html = (ROOT / "index.html").read_text(encoding="utf-8")
    parts = {
        "atlas-graph": (ROOT / "graph.json").read_text(encoding="utf-8").strip(),
        "atlas-proofs": (ROOT / "proofs.json").read_text(encoding="utf-8").strip(),
        "atlas-narratives": (ROOT / "narratives.json").read_text(encoding="utf-8").strip(),
    }
    js = [(ROOT / n).read_text(encoding="utf-8") for n in ("atlas.js", "ui.js")]
    assert html.count(SCRIPTS) == 1
    assert html.count(TITLE) == 1
    for name, data in parts.items():
        assert "</script" not in data.lower(), name + " needs HTML script-safe encoding"
        json.loads(data)
    assert all("</script" not in text.lower() for text in js)
    insertion = "\n".join(
        '<script id="' + name + '" type="application/json">' + data + "</script>"
        for name, data in parts.items()
    )
    insertion += '\n<script id="atlas-model-js">' + js[0] + '</script>'
    insertion += '\n<script id="atlas-ui-js">' + js[1] + '</script>'
    return html.replace(SCRIPTS, insertion).replace(TITLE, BUNDLED)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    output = ROOT / "play.html"
    expected = build()
    if args.write:
        output.write_text(expected, encoding="utf-8")
        print("WROTE", output, len(expected.encode("utf-8")), "bytes")
        return 0
    if not output.is_file() or output.read_text(encoding="utf-8") != expected:
        print("OUTDATED_ATLAS_BUNDLE: run python apps/proof-atlas/build_play.py --write", file=sys.stderr)
        return 1
    print("ATLAS_STANDALONE_MATCHES_SOURCES")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
