#!/usr/bin/env python3
"""Universal local GH 2-jet Ricci computation in canonical second-order gauge.

For arbitrary positive h, gradient p and symmetric Hessian Q with tr Q = 0,
set H=h+p.x+(x Q x)/2, A=-(x cross p)/2-(x cross (Qx))/3.
Then curl(A)=grad(H) exactly (for trace-free Q). At x=0 the entire
5D Ricci tensor of ds5²=-dt²+H|dx|²+H^-1(dpsi+A)² vanishes.

This is a polynomial/rational identity in arbitrary independent h,p,Q jet
variables; no sampling. Extending from a canonical jet gauge to all local
smooth data uses gauge and jet naturality, not formalized in Lean here.
"""
import sympy as s
from itertools import product
h=s.symbols('h',positive=True)
p=s.symbols('p0:3',real=True)
q00,q01,q02,q11,q12=s.symbols('q00 q01 q02 q11 q12',real=True)
Q=s.Matrix([[q00,q01,q02],[q01,q11,q12],[q02,q12,-q00-q11]])
xyz=s.symbols('x y z',real=True)
x=s.Matrix(xyz)
pv=s.Matrix(p)
H=h+pv.dot(x)+(x.T*Q*x)[0]/2
A= -x.cross(pv)/2-x.cross(Q*x)/3
curl=s.Matrix([s.diff(A[2],xyz[1])-s.diff(A[1],xyz[2]),
               s.diff(A[0],xyz[2])-s.diff(A[2],xyz[0]),
               s.diff(A[1],xyz[0])-s.diff(A[0],xyz[1])])
for i in range(3):
    assert s.expand(curl[i]-s.diff(H,xyz[i]))==0
assert s.expand(sum(s.diff(H,z,z) for z in xyz))==0
print('PASS: universal canonical gauge curl(A)=grad(H), Delta H=0',flush=True)

first=s.Matrix(3,3,lambda i,j:s.diff(A[i],xyz[j]).subs({z:0 for z in xyz}))
second=[s.Matrix(3,3,lambda k,l:s.diff(A[i],xyz[k],xyz[l]).subs({z:0 for z in xyz})) for i in range(3)]
for i,j,k in product(range(3),repeat=3):
    assert s.expand(second[i][j,k]-second[i][k,j])==0

n=5
D=[s.zeros(n) for _ in range(n)]
DD=[[s.zeros(n) for _ in range(n)] for _ in range(n)]
# Coordinate index 1..3 corresponds to spatial x,y,z; index 0=t,4=psi.
for coord in range(1,4):
    v=coord-1
    for i in range(1,4):
        D[coord][i,i]=p[v]
        D[coord][i,4]=D[coord][4,i]=first[i-1,v]/h
    D[coord][4,4]=-p[v]/h**2
for dk,dl in product(range(1,4), repeat=2):
    k,l=dk-1,dl-1
    for i,j in product(range(1,4),repeat=2):
        DD[dk][dl][i,j]=Q[k,l]*(1 if i==j else 0)+(
            first[i-1,k]*first[j-1,l]+first[i-1,l]*first[j-1,k])/h
    for i in range(1,4):
        DD[dk][dl][i,4]=DD[dk][dl][4,i]=(
            second[i-1][k,l]/h-(p[k]*first[i-1,l]+p[l]*first[i-1,k])/h**2)
    DD[dk][dl][4,4]=2*p[k]*p[l]/h**3-Q[k,l]/h**2

inv=[-s.Integer(1),1/h,1/h,1/h,h]
# Calculating ∂_k Γ^a_bc uses inverse differentiation -G^-1 (∂_k G) G^-1.
gamma={}
def G(a,b,c):
    if (a,b,c) not in gamma:
        gamma[a,b,c]=s.expand(inv[a]*(D[b][a,c]+D[c][a,b]-D[a][b,c])/2)
    return gamma[a,b,c]
def dGamma(k,a,b,c):
    # Since inverse at the point is diagonal, only its derivative gives mixed m.
    v=0
    for m in range(n):
        dsinv=-inv[a]*D[k][a,m]*inv[m]
        if dsinv!=0:
            v += dsinv*(D[b][m,c]+D[c][m,b]-D[m][b,c])
    v+=inv[a]*(DD[k][b][a,c]+DD[k][c][a,b]-DD[k][a][b,c])
    return s.expand(v/2)

R=s.zeros(n)
for b,c in product(range(n),repeat=2):
    result=0
    for a in range(n):
        result += dGamma(a,a,b,c)-dGamma(c,a,b,a)
        for d in range(n):
            result += G(a,b,c)*G(d,a,d)-G(a,b,d)*G(d,c,a)
    R[b,c]=s.cancel(s.expand(result))
    assert R[b,c]==0, ('Ricci',b,c,s.factor(R[b,c]))
print('PASS: all 25 Ricci components vanish symbolically for 9 independent GH jet parameters',flush=True)
print('SCOPE: local gauge, trace-free Hessian, general smooth metric not yet proved in Lean')
