#!/usr/bin/env python3
"""Reproducibly assemble the complete offline browser edition.

No outside libraries, network requests, asset downloads, or template engines.
Only the audited on-disk engine/UI/research files are embedded into play.html.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
MARKER = '<script src="./engine.js"></script>\n<script src="./ui.js"></script>'
TITLE = "<title>PRIMITIVE FOUNDRY — 工場を育てる</title>"
STANDALONE_TITLE = "<title>PRIMITIVE FOUNDRY — 携帯で動く工場</title>"


def build() -> str:
    page = (ROOT / "index.html").read_text(encoding="utf-8")
    engine = (ROOT / "engine.js").read_text(encoding="utf-8")
    ui = (ROOT / "ui.js").read_text(encoding="utf-8")
    graph = (ROOT / "tech.json").read_text(encoding="utf-8").strip()
    assert page.count(MARKER) == 1, "unexpected script references"
    assert page.count(TITLE) == 1, "unexpected page title"
    assert all("</script" not in text for text in (engine, ui, graph)), "script escape required"
    replacement = (
        '<script type="application/json" id="factory-tech">' + graph
        + '</script>\n<script id="factory-engine">' + engine
        + '</script>\n<script id="factory-ui">' + ui + '</script>'
    )
    return page.replace(MARKER, replacement).replace(TITLE, STANDALONE_TITLE)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true", help="update play.html in place")
    parser.add_argument("--check", action="store_true", help="require play.html to match source exactly")
    args = parser.parse_args()
    if args.write and args.check:
        parser.error("--write and --check are mutually exclusive")
    built = build()
    output = ROOT / "play.html"
    if args.write:
        output.write_text(built, encoding="utf-8")
        print("WROTE", output, "bytes", len(built.encode("utf-8")))
        return 0
    actual = output.read_text(encoding="utf-8")
    if actual != built:
        print("STANDALONE_STALE: regenerate via python games/primitive-foundry/build_play.py --write", file=sys.stderr)
        return 1
    print("STANDALONE_MATCHES_SOURCES")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
