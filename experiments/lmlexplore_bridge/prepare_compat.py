#!/usr/bin/env python3
"""Stage the exact Lean 4.36 Elastica.Variation used by the bridge."""

import hashlib
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent.parent / "lean" / "Elastica" / "Variation.lean"
EXPECTED_GIT_BLOB = "090ac5d63a449623d729505cf685115cd088d666"
TARGET = HERE / "compat" / "Elastica" / "Variation.lean"


def main() -> None:
    source = SOURCE.read_bytes()
    actual = hashlib.sha1(b"blob " + str(len(source)).encode() + b"\0" + source).hexdigest()
    if actual != EXPECTED_GIT_BLOB:
        raise RuntimeError(f"Review the Elastica migration source: {actual} != {EXPECTED_GIT_BLOB}")
    TARGET.parent.mkdir(parents=True, exist_ok=True)
    TARGET.write_bytes(source)
    print("Staged canonical Elastica.Variation Git blob:", actual)


if __name__ == "__main__":
    main()
