#!/usr/bin/env python3
"""Universal local 5D KK -> 4D EMD *off-shell* Ricci equivalence in normal/gauge jets.

At an arbitrary 4D point choose g4=diag(-1,1,1,1), first partials
of g4 zero (Lorentzian normal coordinates) and A_mu=0 (circle gauge).
H=e^(phi/sqrt(3))=q>0. The jets q, ∂q, ∂²q, ∂A, ∂²A,
∂²g4 are otherwise independent and generic, respecting interchange of
commuting second derivatives and metric symmetry. This is a UNIVERSAL
symbolic algebra identity in independent 2-jets, NOT just a sample.

Identity at this point (S0 = Box(log q) + q^-3 F²/4):
  Ric5_mu,nu = E_mu,nu - g_mu,nu S0/2,
  Ric5_mu,5  = -g_mu,nu M^nu/2,
  Ric5_55    = q^-3 S0,
where E is the 4D Ricci-form Einstein-EMD residual, M=∇(q^-3 F),
and sqrt(3)*S0 is the canonical scalar residual.
Tensoriality + gauge covariance are the external geometric bridge
that extends the pointwise normal/gauge calculation to general charts.
"""
import sympy as s
from itertools import product

n=4; N=5
q=s.symbols('q',positive=True)
eta=(-1,1,1,1)
p=s.symbols('p0:4')
q2={(i,j):s.symbols('q%d%d'%(min(i,j),max(i,j))) for i,j in product(range(n),repeat=2)}
# 4D g_{mu,nu,ij}: symmetric in (mu,nu), and in (i,j).
g2={(i,j,k,l):s.symbols('g%d%d_%d%d'%(min(i,j),max(i,j),min(k,l),max(k,l))) for i,j,k,l in product(range(n),repeat=4)}
B={(mu,k):s.symbols('b%d_%d'%(mu,k)) for mu,k in product(range(n),repeat=2)}
C={(mu,k,l):s.symbols('c%d_%d%d'%(mu,min(k,l),max(k,l))) for mu,k,l in product(range(n),repeat=3)}

def der(i,j,k):
    return g2[(i,j,k,k)]

D=[s.zeros(N) for _ in range(N)]
DD=[[s.zeros(N) for _ in range(N)] for _ in range(N)]
for k in range(n):
    for mu in range(n):
        D[k][mu,mu]=p[k]*eta[mu]
        D[k][mu,4]=D[k][4,mu]=B[mu,k]/q**2
    D[k][4,4]=-2*p[k]/q**3
for k,l in product(range(n),repeat=2):
    for mu,nu in product(range(n),repeat=2):
        DD[k][l][mu,nu]=q2[k,l]*eta[mu]*(1 if mu==nu else 0)+q*g2[mu,nu,k,l]+(
            B[mu,k]*B[nu,l]+B[mu,l]*B[nu,k])/q**2
    for mu in range(n):
        DD[k][l][mu,4]=DD[k][l][4,mu]=C[mu,k,l]/q**2-2*(p[k]*B[mu,l]+p[l]*B[mu,k])/q**3
    DD[k][l][4,4]=6*p[k]*p[l]/q**4-2*q2[k,l]/q**3

inv=[eta[i]/q for i in range(n)]+[q*q]
gamma={}
def G(a,b,c):
    if (a,b,c) not in gamma:
        gamma[a,b,c]=s.expand(inv[a]*(D[b][a,c]+D[c][a,b]-D[a][b,c])/2)
    return gamma[a,b,c]
def dGamma(k,a,b,c):
    term=0
    for m in range(N):
        term+=(-inv[a]*D[k][a,m]*inv[m])*(D[b][m,c]+D[c][m,b]-D[m][b,c])
    term+=inv[a]*(DD[k][b][a,c]+DD[k][c][a,b]-DD[k][a][b,c])
    return s.expand(term/2)

Ric=s.zeros(N)
for mu,nu in product(range(N),repeat=2):
    vv=0
    for aa in range(N):
        vv+=dGamma(aa,aa,mu,nu)-dGamma(nu,aa,mu,aa)
        for bb in range(N):
            vv+=G(aa,mu,nu)*G(bb,aa,bb)-G(aa,mu,bb)*G(bb,nu,aa)
    Ric[mu,nu]=s.cancel(s.expand(vv))

# The metric g4 is normal at the point, so all 4D Christoffels vanish.
R4=s.zeros(n)
for mu,nu in product(range(n),repeat=2):
    R4[mu,nu]=s.expand(sum(eta[aa]/2*(
      g2[aa,nu,aa,mu]+g2[aa,mu,aa,nu]-g2[mu,nu,aa,aa]
      -g2[aa,aa,mu,nu]) for aa in range(n)))
F=s.Matrix(n,n,lambda mu,nu:B[nu,mu]-B[mu,nu])
F2=s.expand(sum(eta[i]*eta[j]*F[i,j]**2 for i,j in product(range(n),repeat=2)))
s0=s.expand(sum(eta[i]*(q2[i,i]/q-p[i]**2/q**2) for i in range(n))+F2/(4*q**3))
E=s.zeros(n)
for mu,nu in product(range(n),repeat=2):
    FF=sum(eta[rho]*F[mu,rho]*F[nu,rho] for rho in range(n))
    E[mu,nu]=s.expand(R4[mu,nu]-s.Rational(3,2)*p[mu]*p[nu]/q**2-
          (FF-eta[mu]*int(mu==nu)*F2/4)/(2*q**3))
M=[s.expand(sum(eta[mu]*eta[nu]*((C[nu,mu,mu]-C[mu,mu,nu])/q**3
                -3*p[mu]*F[mu,nu]/q**4) for mu in range(n))) for nu in range(n)]

for mu,nu in product(range(N),repeat=2):
    if mu==4 and nu==4:
        expected=s0/q**3
    elif nu==4:
        expected=-eta[mu]*M[mu]/2
    elif mu==4:
        expected=-eta[nu]*M[nu]/2
    else:
        expected=E[mu,nu] - (eta[mu]*s0/2 if mu==nu else 0)
    diff=s.cancel(s.expand(Ric[mu,nu]-expected))
    assert diff==0,('universal KK reduction',mu,nu,s.factor(diff))
# General 5D scalar curvature, needed for the Einstein-Hilbert action.
trace_R5=s.expand(sum(inv[a]*Ric[a,a] for a in range(N)))
trace_R4=s.expand(sum(eta[a]*R4[a,a] for a in range(n)))
kinetic=s.expand(sum(eta[a]*p[a]**2 for a in range(n))/q**2)
box_log=s.expand(sum(eta[a]*(q2[a,a]/q-p[a]**2/q**2) for a in range(n)))
expected_scalar=(trace_R4-box_log-s.Rational(3,2)*kinetic-F2/(4*q**3))/q
assert s.cancel(trace_R5-expected_scalar)==0
# 5D density is q times 4D density at A(p)=0 and g4=eta.
# Hence q*R5=R4 -1.5(dlogq)^2 -q^-3 F²/4-Box logq.
assert s.cancel(q*trace_R5-(trace_R4-s.Rational(3,2)*kinetic-F2/(4*q**3)-box_log))==0
print('PASS: universal off-shell scalar/density reduction including divergence term')
print('PASS: all 25 universal off-shell 5D-to-EMD Ricci jet identities')
print('PASS: independent 4D metric, Maxwell and scalar jets; no equations assumed')
print('SCOPE: Lorentzian normal coordinates, A(p)=0 gauge; geometric naturality external to Lean')
