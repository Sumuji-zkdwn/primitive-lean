"""Exact combinatorics for the two-arc, four-orientation word model.
Original two HTMLs use smoother endpoint-tangent constraints. Here A/B
are circular arcs and their concatenations are piecewise smooth.
All endpoint coordinates are in units xi=2h/(3pi); costs in c0=pi^2/(8h).
"""
from collections import Counter, defaultdict
from itertools import combinations
from math import pi

Z = {'A': (3, 3), 'B': (-1, 1)}
K = {'A': 1, 'B': -1}  # orientations modulo 4
C = {'A': 1, 'B': 9}   # bending cost in units c0

def rotate(point, j):
    x, y = point
    for _ in range(j % 4):
        x, y = -y, x
    return x, y

def extended_state(word):
    x = y = turn = cost = doubled_area_cross = 0
    for a in word:
        dx, dy = rotate(Z[a], turn)
        doubled_area_cross += x*dy - y*dx
        x, y = x+dx, y+dy
        turn = (turn + K[a]) % 4
        cost += C[a]
    return (x, y, turn, cost, doubled_area_cross)

def state(word):
    return extended_state(word)[:4]

# Two-letter distinction: input x alone cannot distinguish AB and BA.
a, b = state('AB'), state('BA')
assert a == (2, 2, 0, 10), a
assert b == (2, -2, 0, 10), b
assert state('AAB') == (1, 5, 1, 11)
assert state('ABA') == (5, 5, 1, 11)

# 20 balanced words; 12 different endpoints, rectangle convex hull.
words = set(''.join('A' if i in sub else 'B' for i in range(6))
            for sub in combinations(range(6), 3))
assert len(words) == 20
points = defaultdict(list)
for w in words:
    x, y, j, c = state(w)
    assert j == 0 and c == 30
    points[x, y].append(w)
assert len(points) == 12
assert min(x for x,y in points) == -2
assert max(x for x,y in points) == 6
assert min(y for x,y in points) == -6
assert max(y for x,y in points) == 6
assert all(p in points for p in [(-2,-6), (-2,6), (6,-6), (6,6)])
assert any(len(ws)>1 for ws in points.values())

# Degree-2 area separates a 6-letter collision, but 8 letters can collide again.
p6, q6 = extended_state("AABBBA"), extended_state("BAAABB")
assert p6[:4] == q6[:4] == (2, 2, 0, 30)
assert p6[4] == 8 and q6[4] == 24
p8, q8 = extended_state("AAAABBBB"), extended_state("AAABBBBA")
assert p8 == q8 == (0, 0, 0, 40, 32)

# General q=4 min-plus dynamic programming for the x-directed input.
def dp(n,u,h=1.0):
    xi = 2*h/(3*pi)
    c0 = pi*pi/(8*h)
    vals = [0.0, float('inf'), float('inf'), float('inf')]
    for _ in range(n):
        dest = [float('inf')]*4
        for j, v in enumerate(vals):
            for a in ('A', 'B'):
                x, _ = rotate(Z[a], j)
                k = (j+K[a])%4
                dest[k] = min(dest[k], v+c0*C[a]-u*xi*x)
        vals = dest
    return min(vals)/n

def theory(u,h=1.0):
    return min(pi*pi/(8*h), 5*pi*pi/(8*h)-2*h*abs(u)/(3*pi))

if __name__ == '__main__':
    print('AB', a, 'BA', b, 'AAB', state('AAB'), 'ABA', state('ABA'))
    print('Balanced words',len(words),'distinct endpoints',len(points))
    print('Area distinguishes six-letter collision:',p6,q6)
    print('Eight-letter collision survives degree-2 area:',p8,q8)
    print('Third-order moment difference: -32*h^3/(9*pi^2) (AAABBBBA minus AAAABBBB)')
    for p,ws in sorted(points.items()):
        print(' endpoint', p, 'words', ', '.join(sorted(ws)))
    threshold=3*pi**3/4
    print('Transition |u|=3*pi^3/4 for h=1 =',threshold)
    for u in (-30.,0.,20.,30.):
        numerical=dp(4000,u)
        expected=theory(u)
        print('u=',u,'DP=',numerical,'closed form=',expected,'abs error=',abs(numerical-expected))
        assert abs(numerical-expected)<0.001
    print('ALL CHECKS PASSED')
