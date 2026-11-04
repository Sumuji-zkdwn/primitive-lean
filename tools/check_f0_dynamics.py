#!/usr/bin/env python3
"""Exact integer smoke checks; not a substitute for Lean --trust=0."""
from math import comb


def mul(a, b, n):
    out = [0] * (n + 1)
    for i, u in enumerate(a[:n + 1]):
        for j, v in enumerate(b[:n + 1 - i]):
            out[i + j] += u * v
    return out


def power(a, k, n):
    out = [1] + [0] * n
    while k:
        if k % 2:
            out = mul(out, a, n)
        k //= 2
        if k:
            a = mul(a, a, n)
    return out


def hanna_rhs(a, n, omit_k3=False):
    out = [0] * (n + 1)
    for k in range(n // 2 + 1):
        for j in range(n - 2 * k + 1):
            if omit_k3 and k == 3 and j:
                continue
            shift = 2 * k + j
            factor = comb(k + j, j) * 2**j
            coeff = power(a, k * k + k * j, n)
            for t in range(n - shift + 1):
                out[shift + t] += factor * coeff[t]
    return out


def hanna_fixed(n, omit_k3=False):
    a = [1] + [0] * n
    for _ in range(n + 3):
        b = hanna_rhs(a, n, omit_k3)
        if a == b:
            return b
        a = b
    raise AssertionError("series fixed point did not stabilize")


def check_rule481(stages=35):
    """All-background update followed by finite light-cone cropping."""
    width = 2 * stages + 5
    c = width // 2
    g = [[0] * width for _ in range(width)]
    g[c][c] = 1
    accumulated = 1
    checkpoints = {0: 1}
    for t in range(1, stages + 1):
        nxt = [[0] * width for _ in range(width)]
        for i in range(width):
            row, up, down = g[i], g[(i - 1) % width], g[(i + 1) % width]
            dst = nxt[i]
            for j in range(width):
                score = row[j] + 2 * (up[j] + down[j] +
                                      row[(j - 1) % width] + row[(j + 1) % width])
                dst[j] = (481 >> score) & 1
        g = nxt
        active = sum(sum(row[c - t:c + t + 1]) for row in g[c - t:c + t + 1])
        accumulated += active
        if t in (1, 2, 34, 35):
            checkpoints[t] = accumulated
    assert checkpoints == {0: 1, 1: 5, 2: 18, 34: 30690, 35: 34634}
    return checkpoints


def main():
    counts = [sum(comb(n, r) * r ** (n - r) for r in range(1, n + 1))
              for n in range(1, 9)]
    assert counts == [1, 3, 10, 41, 196, 1057, 6322, 41393]
    official = hanna_fixed(8)
    omitted = hanna_fixed(8, True)
    assert official == [1, 2, 5, 14, 50, 220, 1107, 6030, 34643]
    assert omitted == [1, 2, 5, 14, 50, 220, 1107, 6022, 34411]
    assert official[7] - omitted[7] == 8
    for score in range(10):
        assert ((481 >> score) & 1) == (1 - ((481 >> (9 - score)) & 1))
    print("F0 counts n=1..8:", counts)
    print("Hanna official through x^8:", official)
    print("Hanna denominator-omitted:", omitted)
    print("Rule 481 cumulative checkpoints:", check_rule481())
    print("Exact-arithmetic smoke tests passed; formal Lean check runs separately.")


if __name__ == "__main__":
    main()
