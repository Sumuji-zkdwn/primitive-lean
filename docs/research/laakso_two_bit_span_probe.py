"""Exact multi-bit shortest walk regression, with gates on opposite sides.

A finite gate graph has two Boolean labels. Bit 0 flips only at a=1/3,
bit 1 flips only at b=2/3; flips are free, horizontal edges have
calibrated cost. Test every ordered pair of heights and all 4 starting
sheets (using XOR graph symmetry) against the *two-gate* sweep formula.

Unlike single-bit roundtrip bounds, this needs a traverse to BOTH gates.
The test is exact rational arithmetic, and does not prove the continuum
Laakso PI counterexample.
"""
from fractions import Fraction as Q
from heapq import heappush, heappop

HEIGHTS = tuple(Q(s) for s in ("0", "1/6", "1/3", "1/2", "2/3", "5/6", "1"))
A, B = Q(1, 3), Q(2, 3)


def gauges():
    return (
        ("identity", lambda t: t),
        ("square", lambda t: t*t),
        ("piecewise", lambda t: (
            t/2 if t <= A else Q(1, 6) + Q(5, 4)*(t-A)
        )),
    )


def graph(phi):
    n = len(HEIGHTS)
    adj = [[] for _ in range(4*n)]

    def add(a,b,w):
        adj[a].append((b,w))
        adj[b].append((a,w))

    for j in range(n-1):
        length = phi(HEIGHTS[j+1]) - phi(HEIGHTS[j])
        assert length > 0
        for bits in range(4):
            add(4*j+bits, 4*(j+1)+bits, length)

    for j,t in enumerate(HEIGHTS):
        if t == A:
            for bits in range(4):
                if not bits & 1:
                    add(4*j+bits,4*j+(bits^1),Q(0))
        if t == B:
            for bits in range(4):
                if not bits & 2:
                    add(4*j+bits,4*j+(bits^2),Q(0))
    return adj


def dijkstra(adj, source):
    distance = {source:Q(0)}
    heap = [(Q(0), source)]
    while heap:
        dist,u = heappop(heap)
        if distance[u]!=dist:
            continue
        for v,w in adj[u]:
            candidate=dist+w
            if v not in distance or candidate < distance[v]:
                distance[v]=candidate
                heappush(heap,(candidate,v))
    return distance


def main():
    checked=0
    for name,phi in gauges():
        adj=graph(phi)
        for i,s in enumerate(HEIGHTS):
            # XOR symmetry makes checking the initial sheet zero sufficient.
            distances=dijkstra(adj,4*i)
            for j,t in enumerate(HEIGHTS):
                l=min(s,t,A,B)
                u=max(s,t,A,B)
                target=4*j+3   # both bits differ
                expected=2*(phi(u)-phi(l))-abs(phi(s)-phi(t))
                assert distances[target]==expected,(name,s,t,distances[target],expected)
                checked += 4  # all possible starting sheets, by automorphism
        print(name, "196 ordered pairs (49 representatives times 4 sheets): PASS")

    assert checked==588
    for name,phi in gauges():
        s=Q(1,2)
        two=2*(phi(B)-phi(A))
        single=max(2*abs(phi(s)-phi(A)),2*abs(phi(B)-phi(s)))
        assert two>single, (name,two,single)
        print(name,"two-bit detour:",str(two),"largest single-bit detour:",str(single))
    print("PASS: 588 ordered-pair instances; two-gate sweep is strictly more costly.")


if __name__=="__main__":
    main()
