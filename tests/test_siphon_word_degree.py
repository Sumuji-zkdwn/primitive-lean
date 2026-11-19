"""Independent exact checks for lean/Research/SiphonWordDegree.lean.

Python standard library only, exact integer polynomial arithmetic. A reduced word
a^{j0} b a^{j1} ... b a^{js} (a = L, b = E L^3) is applied to the line
(u, v) = (t, 2t) + (0, 0); along this line the leading forms of all maps that occur
(powers of linear forms nonzero at (1, 2)) do not vanish, so the univariate degree
equals the total degree. Checked:

* every reduced word with one b and with two b's has degree 18^m,
  m = 1 + #{interior exponents != 3};
* (ba)^n has degree 18^n for n <= 3 and (ba^3)^n has degree 18 for n <= 6;
* on a few bivariate monomial expansions of low degree (one block) the total degree
  agrees with the line restriction.
"""
from __future__ import annotations

import itertools
import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean' / 'Research' / 'SiphonWordDegree.lean'


def norm(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return tuple(p)


def add(p, q):
    n = max(len(p), len(q))
    return norm([(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)])


def neg(p):
    return tuple(-c for c in p)


def sub(p, q):
    return add(p, neg(q))


def mul(p, q):
    if not p or not q:
        return ()
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                out[i + j] += a * b
    return norm(out)


def power(p, n):
    out = (1,)
    for _ in range(n):
        out = mul(out, p)
    return out


def L(z):
    u, v = z
    return (v, sub(v, u))


def E(z):
    u, v = z
    r = add(v, power(u, 3))
    x = add(u, power(r, 2))
    return (x, sub(r, power(x, 3)))


def B(z):
    return E((neg(z[0]), neg(z[1])))


def Lpow(k, z):
    for _ in range(k):
        z = L(z)
    return z


def deg(z):
    return max(len(z[0]), len(z[1])) - 1


LINE = ((0, 1), (0, 2))  # (t, 2t)


def apply_word(j0, inner, js, z=LINE):
    z = B(Lpow(js, z))
    for j in inner:
        z = B(Lpow(j, z))
    return Lpow(j0, z)


def blocks(inner):
    return 1 + sum(1 for j in inner if j != 3)


class WordDegrees(unittest.TestCase):
    def test_one_and_two_b(self):
        for j0, js in itertools.product(range(6), repeat=2):
            self.assertEqual(deg(apply_word(j0, [], js)), 18)
            for j in range(1, 6):
                self.assertEqual(deg(apply_word(j0, [j], js)), 18 ** blocks([j]), (j0, j, js))

    def test_examples(self):
        for n in range(1, 4):
            self.assertEqual(deg(apply_word(0, [1] * (n - 1), 1)), 18 ** n)
        for n in range(1, 7):
            self.assertEqual(deg(apply_word(0, [3] * (n - 1), 3)), 18)

    def test_bivariate_agrees_on_one_block(self):
        # exact bivariate expansion as dict {(i, j): c} for one block
        def badd(p, q):
            out = dict(p)
            for k, c in q.items():
                out[k] = out.get(k, 0) + c
            return {k: c for k, c in out.items() if c}

        def bneg(p):
            return {k: -c for k, c in p.items()}

        def bmul(p, q):
            out = {}
            for (a, b), c in p.items():
                for (d, e), f in q.items():
                    out[(a + d, b + e)] = out.get((a + d, b + e), 0) + c * f
            return {k: c for k, c in out.items() if c}

        def bpow(p, n):
            out = {(0, 0): 1}
            for _ in range(n):
                out = bmul(out, p)
            return out

        def bdeg(p):
            return max(a + b for a, b in p)

        u, v = {(1, 0): 1}, {(0, 1): 1}
        for js in range(6):
            z = (u, v)
            for _ in range(js):
                z = (z[1], badd(z[1], bneg(z[0])))
            w = (bneg(z[0]), bneg(z[1]))
            r = badd(w[1], bpow(w[0], 3))
            x = badd(w[0], bpow(r, 2))
            y = badd(r, bneg(bpow(x, 3)))
            self.assertEqual((bdeg(x), bdeg(y)), (6, 18))
            self.assertEqual(deg(apply_word(0, [], js)), max(bdeg(x), bdeg(y)))


class LeanSource(unittest.TestCase):
    def test_no_holes_and_declarations(self):
        source = LEAN.read_text(encoding='utf-8')
        self.assertIsNone(re.search(r'^\s*(axiom|sorry)\b', source, re.M))
        self.assertNotIn('sorry', source)
        self.assertNotIn('native_decide', source)
        for name in ('EIter_degrees', 'word_degree', 'deg_ba_pow', 'deg_ba3_pow', 'eval_word'):
            self.assertIsNotNone(re.search(r'^theorem ' + name + r'\b', source, re.M), name)


if __name__ == '__main__':
    unittest.main()
