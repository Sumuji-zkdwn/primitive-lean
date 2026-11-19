"""Independent checks for lean/Research/F16CayleyDickson.lean.

Python standard library only.

* The `epsTable`/`eps` text copied into the Lean module is byte-identical to
  the definition in linear_input/lean_check/F16Holonomy.inc.
* The table is recomputed from the actual Cayley-Dickson multiplication
  (a, b)(c, d) = (ac - conj(d) b, d a + b conj(c)) on coefficient vectors of
  length 16 (not from the sign recursion of the Lean file): e_i e_j must be
  +- e_(i xor j) with exactly the tabulated sign.
* Identities proved in Lean for every level are rechecked on levels 0..5.
"""
from __future__ import annotations

import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean' / 'Research' / 'F16CayleyDickson.lean'
HOLONOMY = ROOT / 'linear_input' / 'lean_check' / 'F16Holonomy.inc'
EPS_DEF = 'def eps (a b : Fin 16) : ℤ := (epsTable[a.val]!)[b.val]!'


def table_block(text):
    start = text.index('def epsTable')
    end = text.index(EPS_DEF) + len(EPS_DEF)
    return text[start:end]


def parse_table(block):
    rows = re.findall(r'#\[(-?1(?:,\s*-?1)*)\]', block)
    return [[int(x) for x in row.split(',')] for row in rows]


def conj(v):
    return [v[0]] + [-x for x in v[1:]]


def add(u, v):
    return [a + b for a, b in zip(u, v)]


def sub(u, v):
    return [a - b for a, b in zip(u, v)]


def mul(x, y):
    n = len(x)
    if n == 1:
        return [x[0] * y[0]]
    h = n // 2
    a, b, c, d = x[:h], x[h:], y[:h], y[h:]
    return sub(mul(a, c), mul(conj(d), b)) + add(mul(d, a), mul(b, conj(c)))


def basis(i, n):
    v = [0] * n
    v[i] = 1
    return v


class CayleyDickson(unittest.TestCase):
    def test_copied_text_is_identical(self):
        lean = table_block(LEAN.read_text(encoding='utf-8'))
        inc = table_block(HOLONOMY.read_text(encoding='utf-8'))
        self.assertEqual(lean, inc)

    def test_table_from_actual_multiplication(self):
        table = parse_table(table_block(HOLONOMY.read_text(encoding='utf-8')))
        self.assertEqual([len(r) for r in table], [16] * 16)
        for i in range(16):
            for j in range(16):
                prod = mul(basis(i, 16), basis(j, 16))
                nonzero = [(k, c) for k, c in enumerate(prod) if c != 0]
                self.assertEqual(len(nonzero), 1, (i, j))
                k, c = nonzero[0]
                self.assertEqual(k, i ^ j)
                self.assertEqual(c, table[i][j], (i, j))

    def test_identities_on_all_levels(self):
        for level in range(0, 6):
            n = 1 << level
            for i in range(n):
                for j in range(n):
                    prod = mul(basis(i, n), basis(j, n))
                    sign = prod[i ^ j]
                    if i == 0 or j == 0:
                        self.assertEqual(sign, 1)
                    elif i == j:
                        self.assertEqual(sign, -1)
                    else:
                        other = mul(basis(j, n), basis(i, n))[i ^ j]
                        self.assertEqual(sign, -other)


class LeanSource(unittest.TestCase):
    def test_no_holes_and_main_declarations_present(self):
        source = LEAN.read_text(encoding='utf-8')
        self.assertIsNone(re.search(r'^\s*(axiom|sorry)\b', source, re.M))
        self.assertNotIn('sorry', source)
        self.assertNotIn('native_decide', source)
        for name in ('eps_eq_cdSign', 'cdSign_zero', 'cdSign_self', 'cdSign_anticomm',
                     'cdSign_succ_low', 'eps_self', 'eps_anticomm', 'eps_low_octonion'):
            self.assertIsNotNone(
                re.search(r'^theorem ' + name + r'\b', source, re.M), name)


if __name__ == '__main__':
    unittest.main()
