"""Exact F16 4x4 observability test from the retained Cayley-Dickson sign table.

Uses rational arithmetic only, without NumPy/SymPy or floating-point rank.
This is a finite certificate, not an independent Lean theorem.
"""
from fractions import Fraction
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'linear_input/lean_check/F16Holonomy.inc'


def sign_table():
    source = SOURCE.read_text(encoding='utf-8')
    body = source.split('def epsTable : Array (Array ℤ) := #[', 1)[1].split('\n]', 1)[0]
    rows = [tuple(int(s.strip()) for s in entry.split(','))
            for entry in re.findall(r'#\[([\d,\s-]+)\]', body)]
    assert len(rows) == 16 and all(len(row) == 16 for row in rows)
    assert all(c in (-1, 1) for row in rows for c in row)
    return rows


def zeros(m, n):
    return [[Fraction(0) for _ in range(n)] for _ in range(m)]


def eye(n):
    a = zeros(n, n)
    for i in range(n):
        a[i][i] = Fraction(1)
    return a


def transpose(a):
    return [list(row) for row in zip(*a)]


def mul(a, b):
    assert len(a[0]) == len(b)
    bt = transpose(b)
    return [[sum((u*v for u, v in zip(row, col)), Fraction(0)) for col in bt]
            for row in a]


def rank_and_det(a):
    b = [[Fraction(v) for v in row] for row in a]
    nr, nc = len(b), len(b[0])
    count, det = 0, Fraction(1)
    for col in range(nc):
        piv = next((r for r in range(count, nr) if b[r][col]), None)
        if piv is None:
            continue
        if count != piv:
            b[piv], b[count] = b[count], b[piv]
            det *= -1
        v = b[count][col]
        det *= v
        for r in range(count+1, nr):
            if b[r][col]:
                fac = b[r][col] / v
                for c in range(col, nc):
                    b[r][c] -= fac * b[count][c]
        count += 1
        if count == nr:
            break
    if nr != nc:
        return count, None
    return count, det if count == nr else Fraction(0)


def run():
    eps = sign_table()
    a, c = zeros(16, 16), zeros(16, 16)
    for j in range(16):
        a[3 ^ j][j] = Fraction(eps[3][j])
        c[10 ^ j][j] = Fraction(eps[10][j])
    assert mul(transpose(a), a) == eye(16)
    u = mul(transpose(a), c)
    assert mul(a, u) == c  # Relative action L(e3)^{-1} L(e10)
    assert mul(mul(u, u), mul(u, u)) == eye(16)

    q = [eps[3][i ^ 9] * eps[10][i] for i in range(8)]
    o = zeros(4, 16)
    for i in range(4):
        o[i][(i+4) ^ 9] = Fraction(q[i+4], 2)
        o[i][i ^ 9] = Fraction(-q[i], 2)

    pieces = []
    power = eye(16)
    for _ in range(4):
        pieces.append(mul(o, power))
        power = mul(power, u)
    cumulative = [sum((p for p in pieces[:j+1]), []) for j in range(4)]
    ranks = [rank_and_det(a_)[0] for a_ in cumulative]
    assert ranks == [4, 8, 12, 16], ranks
    rank_full, determinant = rank_and_det(cumulative[-1])
    assert rank_full == 16 and determinant == Fraction(-1, 256), determinant
    um_i = [[u[i][j] - (1 if i == j else 0) for j in range(16)]
            for i in range(16)]
    assert rank_and_det(um_i)[0] == 12  # Four +1 eigenvectors

    # Reconstruction with each of the 16 standard basis vectors.
    for j in range(16):
        v = [Fraction(int(i == j)) for i in range(16)]
        traces = [[sum((p[i][k]*v[k] for k in range(16)), Fraction(0))
                   for i in range(4)] for p in pieces]
        out = [Fraction(0) for _ in range(16)]
        for i in range(4):
            out[i] = traces[3][i] - traces[1][i]
            out[i+4] = traces[3][i] + traces[1][i]
            out[i ^ 9] = q[i] * (traces[2][i] - traces[0][i])
            out[(i+4) ^ 9] = q[i+4] * (traces[2][i] + traces[0][i])
        assert out == v, (j, out)

    return {'source': 'linear_input/lean_check/F16Holonomy.inc',
            'ranks': ranks, 'undetected_dims': [16-r for r in ranks],
            'determinant': str(determinant), 'fixed_dim_plus_one': 4,
            'period': 4, 'basis_reconstruction_tests': 16,
            'output_support': [[[j, str(v)] for j, v in enumerate(row) if v] for row in o]}


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
