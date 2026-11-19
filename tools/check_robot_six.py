"""Exact, independent enumeration in Z[X]/(X^2-X+1). Standard library only."""

import json
from itertools import product


def power_basis():
    # X*(a+bX) = -b + (a+b)X. Keep the seventh value to check periodicity.
    powers = [(1, 0)]
    for _ in range(6):
        a, b = powers[-1]
        powers.append((-b, a + b))
    assert powers[6] == powers[0]
    return powers[:6]


def polynomial_remainder(counts):
    # Monic long division in ascending coefficient order, independent of power_basis.
    p = counts.copy()
    for i in range(len(p) - 1, 1, -1):
        value = p[i]
        p[i] = 0
        p[i - 1] += value
        p[i - 2] -= value
    return tuple(p[:2])


def trace(word, powers):
    # Walk directed edges in Z/6, updating heading after '+' and before '-'.
    residue, a, b = 0, 0, 0
    residues = []
    for letter in word:
        following = (residue + (1 if letter == "+" else -1)) % 6
        edge = residue if letter == "+" else following
        x, y = powers[edge]
        a, b = a + x, b + y
        residues.append(edge)
        residue = following

    # Recompute the edge histogram from lifted endpoints on Z.
    counts = [0] * 6
    lifted_edges = []
    j = 0
    for letter in word:
        k = j + (1 if letter == "+" else -1)
        edge = min(j, k)
        lifted_edges.append(edge)
        counts[edge % 6] += 1
        j = k
    assert residues == [i % 6 for i in lifted_edges]
    assert polynomial_remainder(counts) == (a, b) and j % 6 == residue
    return {"word": word, "lifted_edges": lifted_edges, "residues": residues,
            "counts": counts, "coefficients": [a, b], "turns": j, "heading": residue}


def enumerate_short():
    powers = power_basis()
    rows = []
    expected = {0: [("", 0)], 6: [("++++++", 0), ("------", 0)],
                7: [("+-----+", 3), ("-+++++-", 3)]}
    for n in range(8):
        returns = []
        total = 0
        for letters in product("+-", repeat=n):
            total += 1
            run = trace("".join(letters), powers)
            if run["coefficients"] == [0, 0]:
                returns.append((run["word"], run["heading"]))
        assert total == 2**n and returns == expected.get(n, [])
        rows.append({"length": n, "words": total, "returns_with_heading": returns})
    assert sum(row["words"] for row in rows) == 255
    return {"order": 6, "basis": ["1", "X"], "powers": powers,
            "witness": trace("-+++++-", powers), "enumeration": rows}


if __name__ == "__main__":
    print(json.dumps(enumerate_short(), indent=2))
