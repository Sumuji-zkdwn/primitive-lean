"""Exact finite analogue of compact vacuum warped-product no-go.

On a connected finite graph, the kernel of the unsigned graph Laplacian
contains only constant functions. On a path with Dirichlet endpoint data,
a nonconstant interior-harmonic function exists. This is NOT a proof of
Bochner's Riemannian theorem or Einstein equations.
"""
import itertools
import sympy as s

def connected(n,edges):
    g=[set() for _ in range(n)]
    for i,j in edges:
        g[i].add(j)
        g[j].add(i)
    seen={0}
    active=[0]
    while active:
        i=active.pop()
        for j in g[i]:
            if j not in seen:
                seen.add(j)
                active.append(j)
    return len(seen)==n

def run():
    counts={}
    for n in range(2,6):
        possible=list(itertools.combinations(range(n),2))
        count=0
        for mask in range(1<<len(possible)):
            edges=[e for j,e in enumerate(possible) if (mask>>j)&1]
            if not connected(n,edges): continue
            L=s.zeros(n)
            for i,j in edges:
                L[i,i]+=1; L[j,j]+=1; L[i,j]-=1; L[j,i]-=1
            assert L.rank()==n-1
            assert L*s.ones(n,1)==s.zeros(n,1)
            assert L.nullspace()==[s.ones(n,1)]
            count+=1
        counts[n]=count
    assert counts=={2:1,3:4,4:38,5:728},counts
    # With fixed endpoints, only middle vertex must be harmonic.
    u=s.Matrix([0,1,2])
    L=s.Matrix([[1,-1,0],[-1,2,-1],[0,-1,1]])
    assert (L*u)[1]==0 and u[0]!=u[2]
    print('PASS: graph harmonic nullity census',counts)
    print('PASS: Dirichlet boundary (0,1,2) yields nonconstant interior harmonic profile')

if __name__=='__main__':
    run()
