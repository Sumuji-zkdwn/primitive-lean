"""Independent exact-arithmetic tests of F16 / Chebyshev / D4 bridges.

Reads the ORIGINAL epsTable from F16Holonomy.inc rather than copying a
second sign convention.  No nonstandard Python packages are required.
Finite checks are not substitutes for Lean verification.
"""
from fractions import Fraction
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "linear_input/lean_check/F16Holonomy.inc"


def original_epsilon_table():
    text = SOURCE.read_text(encoding="utf-8")
    body = text.split("def epsTable", 1)[1].split("\n]\n", 1)[0]
    rows = re.findall(r"#\[\s*([0-9,\s-]+?)\s*\]", body)
    table = [[int(x.strip()) for x in row.split(",")] for row in rows]
    assert len(table) == 16 and all(len(row) == 16 for row in table)
    assert all(abs(e) == 1 for row in table for e in row)
    return table


def matrix(table, t):
    out = [[0 for _ in range(16)] for _ in range(16)]
    for j in range(16):
        out[3 ^ j][j] += table[3][j]
        out[10 ^ j][j] += t * table[10][j]
    return out


def eliminate(rows, *, determinant=False):
    a = [[Fraction(v) for v in row] for row in rows]
    nr, nc = len(a), len(a[0])
    row = 0
    d = Fraction(1)
    for col in range(nc):
        pivot = next((i for i in range(row, nr) if a[i][col]), None)
        if pivot is None:
            if determinant:
                return 0
            continue
        if pivot != row:
            a[pivot], a[row] = a[row], a[pivot]
            d = -d
        p = a[row][col]
        d *= p
        for j in range(col, nc):
            a[row][j] /= p
        for i in range(row + 1, nr):
            f = a[i][col]
            if f:
                for j in range(col, nc):
                    a[i][j] -= f * a[row][j]
        row += 1
        if row == min(nr, nc):
            break
    if determinant:
        assert nr == nc
        return d if row == nc else 0
    return row


def apply(M, v):
    return (M[0][0] * v[0] + M[0][1] * v[1],
            M[1][0] * v[0] + M[1][1] * v[1])


def check():
    table = original_epsilon_table()
    for a in range(8):
        partner = a ^ 9
        alpha, delta = table[3][a], table[3][partner]
        beta, gamma = table[10][partner], table[10][a]
        p, q = alpha * beta, delta * gamma
        assert p * q == (-1 if a < 4 else 1)
        for t in (-3, -1, 0, 1, 3):
            block = [[alpha, t * beta], [t * gamma, delta]]
            normalized = [[alpha * block[0][0], alpha * block[0][1]],
                          [delta * block[1][0], delta * block[1][1]]]
            assert normalized == [[1, t * p], [t * q, 1]]

    qturn = lambda v: (-v[1], v[0])
    mirror = lambda v: (v[1], v[0])
    for v in ((1, 2), (0, 1), (-5, 7)):
        assert qturn(qturn(qturn(qturn(v)))) == v
        assert mirror(mirror(v)) == v
        assert mirror(qturn(mirror(v))) == qturn(qturn(qturn(v)))
        gauge = lambda x: (x[0] - x[1], x[0] + x[1])
        reflect = lambda x: (-x[0], x[1])
        assert gauge(mirror(v)) == reflect(gauge(v))

    for t in (-3, -2, -1, 0, 1, 2, 3):
        A = matrix(table, t)
        rank = eliminate(A)
        det = eliminate(A, determinant=True)
        assert rank == (12 if t in (-1, 1) else 16), (t, rank)
        assert det == (1 - t * t) ** 4 * (1 + t * t) ** 4, (t, det)
        delta = 432 * (1 - t * t)
        assert det == ((1 + t * t) * delta // 432) ** 4
        assert (rank == 12) == (delta == 0)
        assert 4 * (t * t - 1) == -(delta // 108)

    plus, minus, zero = matrix(table, 1), matrix(table, -1), matrix(table, 0)
    assert eliminate(plus) == eliminate(minus) == 12
    assert eliminate(plus + minus) == 16
    assert eliminate(zero) == 16
    for i in range(16):
        for j in range(16):
            assert plus[i][j] + minus[i][j] == 2 * zero[i][j]

    # WFS Möbius reflection in the w=z/(1+z) observation gauge.
    for z in map(Fraction, ["-2/5", "-1/4", "0", "1/3", "2"]):
        m = -z / (1 + 2 * z)
        gauge = lambda x: x / (1 + x)
        assert gauge(m) == -gauge(z)
        assert -m / (1 + 2 * m) == z

    print("F16/WFS/Chebyshev/D4 exact smoke checks: PASS")


if __name__ == "__main__":
    check()
