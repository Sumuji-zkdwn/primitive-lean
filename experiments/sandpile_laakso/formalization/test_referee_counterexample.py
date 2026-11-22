"""Adversarial, standard-library-only verification of the Laakso PI counterexample.

Checks exact rational cell lengths, shared global fiber diameters in finite
ternary gate graphs, and the arithmetic entering an independent all-scale PI
obstruction. Finite checks DO NOT by themselves establish the infinite PI result.
"""
from __future__ import annotations
import heapq
from fractions import Fraction as F

J = F(47, 52)
L = 1 / J


def overlap(x: F, left: F, right: F) -> F:
    return max(F(0), min(x, right) - left)


def deficit_tail(n: int) -> F:
    """Exact sum from n to infinity of (3^-k/3)*(1-3^-k)^2."""
    q = F(1, 3**n)
    return q/2 - 3*q*q/4 + 9*q*q*q/26


def good_phi(s: F) -> F:
    return (F(89,104)*min(s, F(2,3)) + max(F(0),s-F(2,3))) / J


def bad_phi(s: F, depth: int) -> F:
    """Exact Phi at s=j/3^depth, including ALL small-scale defects."""
    if s == 0:
        return F(0)
    assert s.denominator <= 3**depth  # enough for this evaluator's grid values
    total = deficit_tail(depth+1)
    for n in range(1,depth+1):
        eps = F(1,3**n)
        ell = eps/3
        center = 3*eps/2
        sl, sr = center-eps*ell/2, center+eps*ell/2
        il, ir = eps+ell,eps+2*ell
        total += (1-eps)*(overlap(s,il,sl)+overlap(s,sr,ir))
    return (s-total)/J


def shortest_from(graph: list[list[tuple[int,F]]], start: int) -> list[F|None]:
    dst: list[F|None] = [None]*len(graph)
    dst[start] = F(0)
    queue = [(F(0),start)]
    while queue:
        du, u = heapq.heappop(queue)
        if dst[u] != du: continue
        for v,w in graph[u]:
            alt = du+w
            if dst[v] is None or alt < dst[v]:
                dst[v]=alt
                heapq.heappush(queue,(alt,v))
    return dst


def gate_graph(depth: int, coord: str) -> list[list[tuple[int,F]]]:
    M=3**depth
    sheets=2**depth
    z=[(good_phi(F(i,M)) if coord=='good' else bad_phi(F(i,M),depth))
       for i in range(M+1)]
    assert z[0]==0 and z[-1]==1
    graph = [[] for _ in range((M+1)*sheets)]
    def link(a,b,c):
        graph[a].append((b,c));graph[b].append((a,c))
    for i in range(M):
        assert z[i+1]>z[i]
        for bits in range(sheets):
            link(i*sheets+bits,(i+1)*sheets+bits,z[i+1]-z[i])
    for i in range(1,M):
        r=i;p=0
        while r%3==0:
            r//=3;p+=1
        bit=1<<p
        for bits in range(sheets):
            if not bits&bit:
                link(i*sheets+bits,i*sheets+(bits^bit),F(0))
    return graph


def fiber_diameters(depth:int,coord:str) -> list[F]:
    """Same-height / same-prefix fiber maximum; via global bit-XOR symmetry."""
    M=3**depth;sheets=2**depth
    graph=gate_graph(depth,coord)
    diameters=[F(0) for _ in range(depth)]
    for i in range(M+1):
        d=shortest_from(graph,i*sheets)
        for m in range(depth):
            prefix=sum(1 << (depth-k) for k in range(1,m+1))
            values=[d[i*sheets+b] for b in range(sheets) if (b&prefix)==0]
            assert None not in values
            diameters[m]=max(diameters[m],max(values))
    return diameters


def analytic_PI_bounds(n:int,lam:int=2):
    """Prove only arithmetic sufficiency of the paper's geometric inequalities."""
    eps=F(1,3**n)
    ell=eps/3
    H=(2*eps-eps*eps)*ell/J
    r=4*H
    # For all large n, the dilation ball stays inside a C_n gate-free chamber.
    assert lam*r < ell/J
    assert lam*r < F(1,2)
    assert 2*J*r <= ell
    # Paper's explicit geometric estimates: mean oscillation >= 1/32,
    # r*mean upper-gradient <= 32*lambda*epsilon.
    energy_bound=4*lam*J*r/ell
    assert energy_bound <= 32*lam*eps
    # New direct non-doubling witness at the same height s=c_n.
    delta = eps*ell/J
    tiny_r = delta/4
    mass_small_upper_factor = eps*ell*tiny_r  # factor 2^-n cancels
    mass_large_lower_factor = 2*ell*delta      # factor 2^-n cancels
    assert mass_large_lower_factor / mass_small_upper_factor == 8/eps
    assert 2*(2-eps)*delta+delta < 32*tiny_r
    return eps,H,r,energy_bound


def main():
    assert deficit_tail(1)==F(5,52)
    assert 1-deficit_tail(1)==J
    assert good_phi(F(1))==bad_phi(F(1),1)==1
    assert good_phi(F(5,9))-good_phi(F(4,9))==F(89,846)
    assert bad_phi(F(5,9),2)-bad_phi(F(4,9),2)==F(260,3807)
    for coord in ('good','bad'):
        for depth in (1,2,3,4):
            diam=fiber_diameters(depth,coord)
            theoretical=[2*L/F(3**(m+1)) for m in range(depth)]
            assert diam==theoretical,(coord,depth,diam,theoretical)
            print(coord,'depth=',depth, 'A_m=',[str(x) for x in diam])
    for lam in (1,2,5,10,100):
        for n in (6,8,10,12,16):
            if F(1,3**n)>F(1,16*lam): continue
            eps,H,r,energy=analytic_PI_bounds(n,lam)
            print('lambda=',lam,'n=',n,'r=',float(r),
                  'energy_upper=',float(energy),'osc_lower=',float(F(1,32)))
    print('PASS: exact graph tests and all-scale obstruction arithmetic.')

if __name__ == '__main__':
    main()