"""Check preserved sources and exact finite curve-word calculations.

This integer/rational replay is separate from the Lean kernel checks. It does
not verify general signature uniqueness or the smooth elastica boundary problem.
"""
from fractions import Fraction
from hashlib import sha256
from itertools import product
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def state(word):
    x = y = turn = cost = cross = 0
    for letter in word:
        dx, dy = (3, 3) if letter == "A" else (-1, 1)
        for _ in range(turn % 4):
            dx, dy = -dy, dx
        cross += x * dy - y * dx
        x, y = x + dx, y + dy
        turn += 1 if letter == "A" else 3
        cost += 1 if letter == "A" else 9
    return x, y, turn, cost, cross


def finite_summary(k):
    words = [w for w in product("AB", repeat=2*k) if w.count("A") == k]
    states = [state(w) for w in words]
    return dict(words=len(words), endpoints=len({s[:2] for s in states}),
                first_level=len({s[:4] for s in states}), with_area=len(set(states)))


def simple_cycles():
    """Every simple directed cycle, modulo starting vertex; labels are retained."""
    cycles = set()
    for start in range(4):
        def visit(vertex, seen, edges):
            for letter, step in (("A", 1), ("B", 3)):
                nxt = (vertex + step) % 4
                trail = edges + ((vertex, letter),)
                if nxt == start:
                    rotations = [trail[i:] + trail[:i] for i in range(len(trail))]
                    cycles.add(min(rotations))
                elif nxt not in seen:
                    visit(nxt, seen | {nxt}, trail)
        visit(start, {start}, ())
    return sorted(cycles)


def audit(root=ROOT):
    errors = []
    ledger = json.loads((root / "sources/curve_word_chain_20261110/provenance.json").read_text("utf-8"))
    for row in ledger["originals"]:
        path = root / row["path"]
        if not path.is_file() or sha256(path.read_bytes()).hexdigest() != row["sha256"]:
            errors.append("Preserved-source hash mismatch: " + row["path"])

    expected = {
        "AB": (2, 2, 4, 10, 0), "BA": (2, -2, 4, 10, 0),
        "AAB": (1, 5, 5, 11, 12), "ABA": (5, 5, 5, 11, 0),
        "AABBBA": (2, 2, 12, 30, 8), "BAAABB": (2, 2, 12, 30, 24),
        "AAAABBBB": (0, 0, 16, 40, 32), "AAABBBBA": (0, 0, 16, 40, 32),
    }
    for word, value in expected.items():
        if state(word) != value:
            errors.append("Exact word mismatch: " + word)
    summaries = {str(k): finite_summary(k) for k in (3, 4)}
    if summaries != {
        "3": dict(words=20, endpoints=12, first_level=12, with_area=20),
        "4": dict(words=70, endpoints=20, first_level=20, with_area=50),
    }:
        errors.append("Balanced-word cardinality mismatch")
    points = {state(w)[:2] for w in product("AB", repeat=6) if w.count("A") == 3}
    corners = {(-2, -6), (-2, 6), (6, -6), (6, 6)}
    if not corners <= points or not all(-2 <= x <= 6 and -6 <= y <= 6 for x, y in points):
        errors.append("Rectangle hull certificate failed")

    cycle_rows = []
    for cycle in simple_cycles():
        cost = dx = 0
        for j, letter in cycle:
            x, y = (3, 3) if letter == "A" else (-1, 1)
            for _ in range(j):
                x, y = -y, x
            cost += 1 if letter == "A" else 9
            dx += x
        cycle_rows.append(dict(edges=cycle, mean_cost=str(Fraction(cost, len(cycle))),
                               mean_dx=str(Fraction(dx, len(cycle)))))
    coefficients = {(row["mean_cost"], row["mean_dx"]) for row in cycle_rows}
    if len(cycle_rows) != 6 or coefficients != {("1", "0"), ("9", "0"), ("5", "1"), ("5", "-1")}:
        errors.append("Simple-cycle coefficient certificate failed")
    return dict(passed=not errors, errors=errors, balanced_words=summaries,
                collision_states={w: state(w) for w in expected}, simple_cycles=cycle_rows,
                normalization="xi=2h/(3pi), c0=pi^2/(8h), t=u*xi/c0; min cycle mean=min(1,5-|t|)",
                scope="Exact finite integer/rational calculation and original-source hashes; Lean and general analytic theorems are checked separately.")


if __name__ == "__main__":
    result = audit()
    out = ROOT / "verification/curve-word-chain.json"
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", "utf-8")
    print(json.dumps(result, ensure_ascii=False, indent=2))
    raise SystemExit(0 if result["passed"] else 1)
