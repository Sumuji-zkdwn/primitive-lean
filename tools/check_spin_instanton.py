"""Exact Euclidean SU(2) instanton from round S4 conformal spin connection.

Checks local connection/curvature/Yang-Mills identities in stereographic
coordinates, using exact rational functions. No physical Lorentzian claim.
"""
import sympy as S
from itertools import combinations

x=S.symbols('x0:4',real=True)
rho2=S.Integer(1)
s=rho2+sum(z*z for z in x)

def eps3(i,j,k):
    if len({i,j,k})<3: return 0
    return (1 if (i,j,k) in ((0,1,2),(1,2,0),(2,0,1)) else -1)

def eta(a,m,n):
    if m==n:return 0
    if m<3 and n<3:return eps3(a,m,n)
    if m<3 and n==3:return int(a==m)
    if m==3 and n<3:return -int(a==n)
    raise AssertionError((a,m,n))

def bracket(A,B,a):
    return sum(eps3(a,b,c)*A[b]*B[c] for b in range(3) for c in range(3))

A=[[2*sum(eta(a,m,n)*x[n] for n in range(4))/s for m in range(4)]
   for a in range(3)]

def run():
    # Round S4 metric radius 1: Ω² δ, Ω=2/(1+|x|²).
    # ω_mu^{ab} = δ^a_mu ∂^b log Ω - δ^b_mu ∂^a log Ω.
    dl=[-2*z/s for z in x]
    for a in range(3):
        for mu in range(4):
            projection=S.Rational(1,2)*sum(eta(a,i,j)*(
                (int(i==mu)*dl[j])-(int(j==mu)*dl[i]))
                for i in range(4) for j in range(4))
            assert S.cancel(projection+A[a][mu])==0

    # F=dA + A∧A is self-dual and Yang-Mills on R4.
    F={}
    for a in range(3):
        for mu,nu in combinations(range(4),2):
            comm=bracket([A[k][mu] for k in range(3)],
                         [A[k][nu] for k in range(3)],a)
            f=S.diff(A[a][nu],x[mu])-S.diff(A[a][mu],x[nu])+comm
            expected=-4*eta(a,mu,nu)/s**2
            assert S.factor(f-expected)==0,(a,mu,nu,S.factor(f-expected))
            F[a,mu,nu]=expected
            F[a,nu,mu]=-expected
        for mu in range(4):
            F[a,mu,mu]=S.Integer(0)
    for a in range(3):
        for mu,nu in combinations(range(4),2):
            star=S.Rational(1,2)*sum(S.LeviCivita(mu,nu,r,j)*F[a,r,j]
                for r in range(4) for j in range(4))
            assert S.factor(F[a,mu,nu]-star)==0,(a,mu,nu)

    # The Euclidean YM equation D_mu F_{mu nu}=0.
    for a in range(3):
        for nu in range(4):
            ym=sum(S.diff(F[a,mu,nu],x[mu])+
                   bracket([A[b][mu] for b in range(3)],
                           [F[c,mu,nu] for c in range(3)],a)
                   for mu in range(4))
            assert S.factor(ym)==0,(a,nu,S.factor(ym))

    # Show curvature is nonzero, while scalar metric is smooth on this patch.
    assert F[0,0,3].subs({z:0 for z in x})==-4
    assert s.subs({z:0 for z in x})==1
    # Action-density contraction scales as (1+r²)^-4.
    norm=sum(F[a,mu,nu]**2 for a in range(3)
             for mu in range(4) for nu in range(4))
    assert S.factor(norm-192/s**4)==0,S.factor(norm)
    print('PASS: spin connection projection, 18 curvature components,')
    print('      18 self-duality identities, 12 source-free YM equations')
    print('F^a_{mu nu}=-4 eta^a_{mu nu}/(1+r²)^2; |F|²=192/(1+r²)^4')

if __name__=='__main__':run()
