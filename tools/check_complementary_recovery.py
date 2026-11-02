"""Exact independent regression for paired observations and F16 recovery.

The actual signed F16 basis table is read from the unchanged Lean source.
Every basis vector is checked, so the rational linear identities are covered
on all of Q^16, in addition to the universal Lean proofs over R.
"""
from fractions import Fraction as Q
from pathlib import Path
import json

from check_f16_unexpected_bridges import original_epsilon_table, matrix, eliminate


ROOT = Path(__file__).resolve().parents[1]


def matvec(a, x):
    return tuple(sum(Q(c) * y for c, y in zip(row, x)) for row in a)


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def scale(c, x):
    return tuple(Q(c) * y for y in x)


def identity(n):
    return [[Q(i == j) for j in range(n)] for i in range(n)]


def inverse(a):
    n = len(a)
    aug = [[Q(x) for x in row] + eye for row, eye in zip(a, identity(n))]
    for j in range(n):
        pivot = next(i for i in range(j, n) if aug[i][j])
        aug[j], aug[pivot] = aug[pivot], aug[j]
        aug[j] = list(scale(1 / aug[j][j], aug[j]))
        for i in range(n):
            if i != j:
                aug[i] = list(sub(aug[i], scale(aug[i][j], aug[j])))
    assert [row[:n] for row in aug] == identity(n)
    return [row[n:] for row in aug]


def pencil(b, c, t):
    return [[x + t * y for x, y in zip(br, cr)] for br, cr in zip(b, c)]


def observe(b, c, x):
    return matvec(pencil(b, c, 1), x), matvec(pencil(b, c, -1), x)


def decode(d, y):
    return matvec(d, scale(Q(1, 2), add(*y)))


def check():
    table = original_epsilon_table()
    b = matrix(table, 0)
    c = [[int((10 ^ j) == i) * table[10][j] for j in range(16)] for i in range(16)]
    d = inverse(b)
    plus, minus = matrix(table, 1), matrix(table, -1)
    assert plus == pencil(b, c, 1) and minus == pencil(b, c, -1)
    assert eliminate(plus) == eliminate(minus) == 12
    assert eliminate(plus + minus) == 16
    assert eliminate(b, determinant=True) == 1
    # This optional numeric identity makes the exact inverse particularly cheap.
    # The Lean decoder uses the certified inverse; B^2=-I is not claimed as a
    # separately formalized F16 theorem in this change.
    assert d == [[-x for x in row] for row in b]
    basis = [tuple(Q(i == j) for i in range(16)) for j in range(16)]
    for x in basis + [tuple(Q(i - 7, i + 1) for i in range(16))]:
        y = (matvec(plus, x), matvec(minus, x))
        restored = decode(d, y)
        assert restored == x
        assert matvec(plus, restored) == y[0]
        assert matvec(minus, restored) == y[1]
        assert scale(Q(1, 2), sub(*y)) == matvec(c, restored)
    # Four independent null vectors per singular probe from the source formula.
    for sign, a in ((1, plus), (-1, minus)):
        for low in range(4, 8):
            x = [Q(0)] * 16
            x[low] = 1
            x[low ^ 9] = sign * (1 if low in (4, 7) else -1)
            assert not any(matvec(a, x))
            other = minus if sign == 1 else plus
            assert any(matvec(other, x))
            assert decode(d, observe(b, c, x)) == tuple(x)
    # Nontrivial invertible pencils in several dimensions over Q.
    for n in (1, 2, 3, 5):
        gb = [[Q(1 if i == j else (i + j + 1 if i < j else 0))
               for j in range(n)] for i in range(n)]
        gc = [[Q((i + 2) * (j + 1) - 3, i + j + 1) for j in range(n)] for i in range(n)]
        gd = inverse(gb)
        for x in identity(n):
            assert decode(gd, observe(gb, gc, x)) == tuple(x)
    # Singular B need not lose information: B=0, C=I.
    assert observe([[0]], [[0]], (Q(0),)) == observe([[0]], [[0]], (Q(1),))
    assert observe([[0]], [[1]], (Q(1),)) == ((Q(1),), (Q(-1),))
    # Char 2: B=C=1 is invertible at t=0, but both probes vanish.
    assert (1 + 1) % 2 == (1 - 1) % 2 == 0
    # An arbitrary observation pair need not be realizable.
    inconsistent = ((Q(1),), (Q(0),))
    rebuilt = observe([[1]], [[0]], decode([[1]], inconsistent))
    assert rebuilt == ((Q(1, 2),), (Q(1, 2),)) and rebuilt != inconsistent
    # PR #19's proven four-phase coordinate form, with even/odd kernels.
    trace = lambda x, u: (x, -u, -x, u)
    for x, u in ((Q(0), Q(1)), (Q(2, 3), Q(-5, 7)), (Q(0), Q(0))):
        y = trace(x, u)
        assert ((y[0] - y[2]) / 2, (y[3] - y[1]) / 2) == (x, u)
        assert trace(0, u)[::2] == (0, 0)
        assert trace(x, 0)[1::2] == (0, 0)
    result = dict(passed=True, arithmetic="fractions.Fraction", f16_basis_vectors=16,
                  f16_kernel_vectors=8, singular_ranks=[12, 12], paired_rank=16,
                  generic_dimensions=[1, 2, 3, 5], counterexample_categories=4,
                  scope="Finite exact regression; universal claims are certified separately by Lean")
    out = ROOT / "verification"
    out.mkdir(exist_ok=True)
    (out / "complementary-recovery-smoke.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    check()
