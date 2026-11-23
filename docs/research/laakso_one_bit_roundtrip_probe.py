"""Independent exact one-bit roundtrip check for finite ternary gate graphs.

All heights and edge lengths are rational. For every height and every bit,
compare the Dijkstra shortest return path that flips that bit against
2 * the calibrated distance to the nearest gate where that bit can flip.

Other-bit flips and arbitrarily many cycles are permitted in Dijkstra.
This is a finite regression check, not the infinite Laakso path theorem.
"""
from fractions import Fraction as Q
from heapq import heappop, heappush


def v3(j):
    p = 0
    while j % 3 == 0:
        j //= 3
        p += 1
    return p


def gauges():
    return (
        ("identity", lambda x: x),
        ("quadratic", lambda x: x*x),
        ("piecewise_good", lambda x: x / 2 if x <= Q(1,3)
         else Q(1,6) + Q(5,4) * (x-Q(1,3))),
    )


def make_graph(depth, phi):
    M, sheets = 3**depth, 2**depth
    z = [phi(Q(j, M)) for j in range(M+1)]
    graph = [[] for _ in range((M+1)*sheets)]
    gates = {p: [] for p in range(depth)}

    def edge(a,b,w):
        graph[a].append((b,w))
        graph[b].append((a,w))

    for j in range(M):
        assert z[j+1] > z[j]
        for b in range(sheets):
            edge(j*sheets+b,(j+1)*sheets+b,z[j+1]-z[j])
    for j in range(1,M):
        p = v3(j)
        assert p < depth
        gates[p].append(j)
        mask = 1 << p
        for b in range(sheets):
            if not b & mask:
                edge(j*sheets+b,j*sheets+(b^mask),Q(0))
    return M,sheets,z,graph,gates


def shortest(graph,src,dst):
    heap = [(Q(0),src)]
    distances = {src:Q(0)}
    while heap:
        cost,v = heappop(heap)
        if cost != distances[v]:
            continue
        if v == dst:
            return cost
        for w,length in graph[v]:
            d = cost+length
            if w not in distances or d < distances[w]:
                distances[w] = d
                heappush(heap,(d,w))
    raise AssertionError("not reachable")


def main():
    count=0
    for label,phi in gauges():
        for depth in range(1,4):
            M,sheets,z,graph,gates=make_graph(depth,phi)
            for j in range(M+1):
                for p in range(depth):
                    target=j*sheets+(1<<p)
                    actual=shortest(graph,j*sheets,target)
                    lower=2*min(abs(z[j]-z[g]) for g in gates[p])
                    assert actual==lower,(label,depth,j,p,actual,lower)
                    count+=1
            print(f"{label} depth={depth}: {(M+1)*depth} exact one-bit roundtrip checks")
    assert count==324
    print("PASS: 324 exact one-bit shortest cost identities.")


if __name__=="__main__":
    main()
