"""Exact finite checks for the equivariant compact-fiber vacuum obstruction."""
import sympy as S
from itertools import combinations_with_replacement

eta = S.diag(-1,1,1,1)
def E(i,j):
    M=S.zeros(4); M[i,j]=1; return M
J=[E(3,2)-E(2,3),E(1,3)-E(3,1),E(2,1)-E(1,2)]
B=[E(0,i)+E(i,0) for i in (1,2,3)]
L=J+B
assert all(M.T*eta+eta*M==S.zeros(4) for M in L)
for i,j,k in [(0,1,2),(1,2,0),(2,0,1)]:
    assert B[i]*B[j]-B[j]*B[i]==-J[k]
    assert B[i]*J[k]-J[k]*B[i]==-B[j]
print('PASS cyclic real boost adjoint eigenvectors and Lorentz generators')
# Invariant symmetric bilinear forms on the adjoint module.
flat=S.Matrix.hstack(*[M.reshape(16,1) for M in L])
ad=[]
for X in L:
    ad.append(S.Matrix.hstack(*[flat.gauss_jordan_solve((X*Y-Y*X).reshape(16,1))[0] for Y in L]))
def symmetric(n):
    inds=list(combinations_with_replacement(range(n),2))
    vs=S.symbols('a:'+str(len(inds)))
    d=dict(zip(inds,vs))
    return S.Matrix(n,n,lambda i,j:d[tuple(sorted((i,j)))]),vs
G,g=symmetric(6)
A,_=S.linear_eq_to_matrix([e for M in ad for e in M.T*G+G*M],g)
assert A.rank()==19
for q in A.nullspace():
    Q=G.subs(dict(zip(g,q)))
    assert Q.trace()==0
assert len(A.nullspace())==2
print('PASS invariant adjoint Gram space has dimension 2 and trace zero; no nonzero PSD form')
# General invariant metric block and one internal covector component.
H,h=symmetric(4)
A,_=S.linear_eq_to_matrix([e for M in L for e in M.T*H+H*M],h)
assert A.rank()==9 and len(A.nullspace())==1
Q=H.subs(dict(zip(h,A.nullspace()[0])))
assert Q==eta or Q==-eta
A=S.Matrix.vstack(*[M.T for M in L]); assert A.rank()==4
print('PASS invariant external metric is scalar Minkowski; mixed block vanishes')
# A constant mixed term can be a coordinate artifact: theta=y+q*x mod 2pi.
q=S.Matrix(S.symbols('q0:4')); R=S.symbols('R', positive=True)
P=S.eye(5); P[4,0:4]=q.T
G0=S.diag(-1,1,1,1,R**2); G1=P.T*G0*P
assert G1[:4,4]==R**2*q
assert G1.det().expand()==-R**2
assert P.inv().T*G1*P.inv()==G0
for M in L:
    N=P.inv()*S.diag(M,0)*P
    assert N.T*G1+G1*N==S.zeros(5)
print('PASS nonzero coordinate mixed terms, conjugated Lorentz lift, and untwisting')
