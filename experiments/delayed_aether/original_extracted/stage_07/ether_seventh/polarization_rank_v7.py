#!/usr/bin/env python3
"""Exact rational linear-algebra audit: six spatial metric components, rank-two TT."""
from pathlib import Path
import sympy as s
import json
D=Path(__file__).resolve().parent
P=s.diag(1,1,0)
I=s.eye(3)
E=[]
for i,j in [(0,0),(1,1),(2,2),(0,1),(0,2),(1,2)]:
    t=s.zeros(3)
    t[i,j]=1;t[j,i]=1
    E.append(t)
def coords(H):return s.Matrix([H[0,0],H[1,1],H[2,2],H[0,1],H[0,2],H[1,2]])
def tt(H):return P*H*P - s.Rational(1,2)*P*s.trace(P*H)
Q=s.Matrix.hstack(*(coords(tt(h)) for h in E))
assert Q.rank()==2
assert Q*Q==Q
k=s.Matrix([0,0,1])
A=s.Matrix.hstack(*(coords(k*s.eye(3)[:,j].T+s.eye(3)[:,j]*k.T) for j in range(3)))
assert A.rank()==3
assert Q*A==s.zeros(6,3)
trace=s.Matrix([1,1,1,0,0,0])
nullspan=s.Matrix.hstack(A,trace)
assert nullspan.rank()==4 and Q*nullspan==s.zeros(6,4)
assert s.Matrix.hstack(Q,nullspan).rank()==6
assert Q.eigenvals()=={s.Integer(1):2,s.Integer(0):4}
out={'spatial_symmetric_components':6,'TT_rank':int(Q.rank()),'TT_eigenvalues':{'one':2,'zero':4},'displacement_strain_span':int(A.rank()),'displacement_plus_scalar_span':int(nullspan.rank()),'kernel_equals_displacement_plus_scalar':True,'TT_projector_matrix':str(Q),'note':'Algebra at nonzero wavevector k=(0,0,1); valid in rotated basis for every nonzero 3-vector.'}
(D/'polarization_rank_v7.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(out,ensure_ascii=False,indent=2))
