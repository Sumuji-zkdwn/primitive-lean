"""Exact finite oracle for temporal sampling and E-rotation aliasing.

It is an arithmetic regression check, not a Lean proof.
For N<=4, every deterministic update and observation map is enumerated.
Equivalence of infinite observation streams is decidable by <= N^2
pair-state visits; the same applies to each sampled block transition.
"""
from itertools import product
from fractions import Fraction
from math import exp


def signatures(update, observe, period, width):
    n = len(update)
    result = []
    for x in range(n):
        x1 = x
        values = []
        for _ in range(period * width):
            values.append(observe[x1])
            x1 = update[x1]
        result.append(tuple(values))
    return result


def check_all(n):
    count = 0
    for update in product(range(n), repeat=n):
        for observe in product(range(n), repeat=n):
            for m in (1, 2, 3):
                width = n*n + 1
                traces = signatures(update, observe, m, width)
                full = [tuple(s[:width]) for s in traces]
                sampled = [tuple(s[::m][:width]) for s in traces]
                full_rel = {(x,y) for x in range(n) for y in range(n)
                            if full[x] == full[y]}
                sample_rel = {(x,y) for x in range(n) for y in range(n)
                              if sampled[x] == sampled[y]}
                assert full_rel <= sample_rel
                compatible = all((update[x],update[y]) in sample_rel
                                 for x,y in sample_rel)
                assert compatible == (sample_rel == full_rel)
                # Every phase j in range(m) recovers all times.
                phases = [tuple(tuple(s[j::m][:width])
                                for j in range(m)) for s in traces]
                phase_rel = {(x,y) for x in range(n) for y in range(n)
                             if phases[x] == phases[y]}
                assert phase_rel == full_rel
            count += 1
    return count


def h(z):
    x,u = z
    return (-u, x)


def xread(z):
    return z[0]


def gwfs(r):
    return (r*r-1.0)/2.0


def check_rotation():
    a = (Fraction(0),Fraction(0))
    b = (Fraction(0),Fraction(1))
    for n in range(15):
        za,zb = a,b
        for _ in range(2*n):
            za,zb=h(za),h(zb)
        assert xread(za)==xread(zb)
        assert gwfs(exp(float(xread(za))))==gwfs(exp(float(xread(zb))))
    assert xread(h(a))!=xread(h(b))
    assert gwfs(exp(float(xread(h(a))))) != gwfs(exp(float(xread(h(b)))))
    for state in product([Fraction(-2),Fraction(-1),Fraction(0),
                          Fraction(1),Fraction(2)],repeat=2):
        assert h(h(state)) == (-state[0], -state[1])


def main():
    totals = {n:check_all(n) for n in range(1,5)}
    assert totals == {1:1, 2:16, 3:729, 4:65536}
    check_rotation()
    print("Temporal sampling exhaustive N<=4:", totals)
    print("Sampling congruence iff full predictive equivalence: PASS")
    print("All-phase recovery for m=1,2,3: PASS")
    print("E quarter-turn even-step aliasing and WFS2: PASS")


if __name__ == "__main__":
    main()
