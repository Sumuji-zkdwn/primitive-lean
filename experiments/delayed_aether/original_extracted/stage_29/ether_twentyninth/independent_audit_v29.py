#!/usr/bin/env python3
"""Independent audit with exact rational matrix algebra and flat-embedding counterexample."""
import json
import sympy as s
from pathlib import Path
ROOT=Path(__file__).resolve().parent

dirs=[s.Matrix(x) for x in [(1,0,0),(0,1,0),(0,0,1),
                            (1,1,0),(1,0,1),(0,1,1),(1,1,1)]]
# Any symmetric metric g generates seven quadratic squared lengths.
E=[s.Matrix([[1,0,0],[0,0,0],[0,0,0]]),s.Matrix([[0,0,0],[0,1,0],[0,0,0]]),s.Matrix([[0,0,0],[0,0,0],[0,0,1]]),
   s.Matrix([[0,1,0],[1,0,0],[0,0,0]]),s.Matrix([[0,0,1],[0,0,0],[1,0,0]]),s.Matrix([[0,0,0],[0,0,1],[0,1,0]])]
L=s.Matrix([[ (v.T*e*v)[0] for e in E] for v in dirs])
resid=s.Matrix([[1,1,1,-1,-1,-1,1]])
assert L.rank()==6 and resid*L==s.zeros(1,6)
assert s.eye(7)-L*(L.T*L).inv()*L.T==resid.T*resid/7

# Exact Euclidean embedding x -> x+eps*y*z, y,z unchanged.
# Global Riemann curvature remains zero: the coordinates give actual Euclidean points.
eps=s.Rational(1,100)
a=s.Rational(1,4)
y=s.Rational(1,3); z=s.Rational(1,7)
def Phi(x,y,z):return s.Matrix([x+eps*y*z,y,z])
base=Phi(0,y,z)
lengths=[]
for v in dirs:
    delta=Phi(a*v[0],y+a*v[1],z+a*v[2])-base
    lengths.append((delta.T*delta)[0])
exact_mismatch=(resid*s.Matrix(lengths))[0]
assert exact_mismatch==2*eps*a**3, (exact_mismatch,2*eps*a**3)
# Affine shear x -> x + eps(y+z) gives zero seven-link mismatch.
def Phi_aff(x,y,z):return s.Matrix([x+eps*(y+z),y,z])
base_a=Phi_aff(0,y,z)
la=[((Phi_aff(a*v[0],y+a*v[1],z+a*v[2])-base_a).T*(Phi_aff(a*v[0],y+a*v[1],z+a*v[2])-base_a))[0] for v in dirs]
assert (resid*s.Matrix(la))[0]==0

# Exact Fourier-symbol calculations with d=(1,2,3).
d=s.Matrix([1,2,3]); k2=(d.T*d)[0]
G=s.Matrix([[2*d[0],0,0],[0,2*d[1],0],[0,0,2*d[2]],
            [d[1],d[0],0],[d[2],0,d[0]],[0,d[2],d[1]]])
sc=s.Matrix([[k2-d[0]**2,k2-d[1]**2,k2-d[2]**2,
              -2*d[0]*d[1],-2*d[0]*d[2],-2*d[1]*d[2]]])
# Reconstruct TT with exact tensor projector; no hard-coded polarization count.
q=s.eye(3)-d*d.T/k2
TT=[]
for e in E:
    P=q*e*q
    TT.append(P-s.Rational(1,2)*q*s.trace(P))
vector=lambda h:s.Matrix([h[0,0],h[1,1],h[2,2],h[0,1],h[0,2],h[1,2]])
TT=s.Matrix.hstack(*[vector(e) for e in TT])
assert TT.rank()==2 and TT*TT==TT and TT*G==s.zeros(6,3)
assert sc*G==s.zeros(1,3) and sc*TT==s.zeros(1,6)

def pi(v):
    px,py,pz,pxy,pxz,pyz=v
    return s.Matrix([[px,pxy/2,pxz/2],[pxy/2,py,pyz/2],[pxz/2,pyz/2,pz]])
M=s.Matrix([[ (pi(s.eye(6)[:,j])*d)[i] for j in range(6)] for i in range(3)])
assert M.rank()==3 and sc*M.T==s.zeros(1,3)
assert s.Matrix.hstack(G,vector(s.eye(3)),*TT.columnspace()).rank()==6

result={
 'exact_link_metric_rank':6, 'exact_metric_remainder_dimension':1,
 'flat_embedding_quadratic_shear_epsilon':str(eps),
 'flat_embedding_spacing':str(a),
 'flat_embedding_seven_edge_residual':str(exact_mismatch),
 'flat_embedding_predicted_residual':str(2*eps*a**3),
 'affine_embedding_residual':0,
 'gauge_rank':G.rank(), 'curvature_rank':sc.rank(),
 'TT_rank':TT.rank(), 'momentum_constraint_rank':M.rank(),
 'scalar_momentum_poisson_bracket_zero':sc*M.T==s.zeros(1,3),
 'constrained_metric_DOF':6-G.rank()-sc.rank(),
 'constrained_phase_space_dimension':12-2*(3+1),
 'status':'all exact rational identities passed',
 'qualification':'vertex displacements can create nonzero finite-stencil link mismatch even in globally flat embedded Euclidean space'
}
(ROOT/'independent_audit_v29.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
print(json.dumps(result,ensure_ascii=False,indent=2))
