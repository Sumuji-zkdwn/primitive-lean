#!/usr/bin/env python3
"""Independent exact checks of general GH closed forms, KK blocks and Hopf algebra.
The 192 closed-form component equalities and 25 block inverses use independent
symbols, not numerical samples. No claim of Lean curvature or quotient proof.
"""
import itertools
import sympy as s
p=s.symbols('p0:3'); da=s.symbols('d0:9')
D=lambda k,j: da[3*k+j] if k<3 and j<3 else s.Integer(0)
curls=[D(1,2)-D(2,1),D(2,0)-D(0,2),D(0,1)-D(1,0)]
e=lambda k,i:int(k==i)
for axis,i,j,k in itertools.product(range(3),range(4),range(4),range(4)):
    def part(d,u,v):
        a,b,c=[(0,1,2),(1,2,0),(2,0,1)][axis]
        return D(d,u)*e(a,v)-D(d,v)*e(a,u)-(p[d] if d<3 else 0)*(e(b,u)*e(c,v)-e(b,v)*e(c,u))
    val=s.sympify(part(i,j,k)+part(j,k,i)+part(k,i,j))
    assert s.expand(val.subs({p[z]:curls[z] for z in range(3)},simultaneous=True))==0
print('PASS: 192 GH first-jet exterior closure identities')
q=s.symbols('q',nonzero=True); aa=s.Matrix(s.symbols('a0:4'))
eta=s.diag(-1,1,1,1); M=s.zeros(5);N=s.zeros(5)
for i in range(4):
    for j in range(4):
        M[i,j]=q**3*eta[i,j]+aa[i]*aa[j];N[i,j]=eta[i,j]
    M[i,4]=M[4,i]=aa[i];N[i,4]=N[4,i]=-eta[i,i]*aa[i]
M[4,4]=1;N[4,4]=q**3+(aa.T*eta*aa)[0]
assert all(s.expand((M*N)[i,j]-(q**3 if i==j else 0))==0
           for i,j in itertools.product(range(5),repeat=2))
v=s.Matrix(s.symbols('v0:4'));b=s.Matrix(s.symbols('b0:4'));t=s.symbols('t')
assert s.expand((t+(aa.T*v)[0])**2-(t+(b.T*v)[0]+((aa-b).T*v)[0])**2)==0
print('PASS: 25 arbitrary-gauge KK block inverses and fibre shift')
X=s.symbols('X0:4'); c,d=s.symbols('c d')
Y=[c*X[0]-d*X[1],d*X[0]+c*X[1],c*X[2]-d*X[3],d*X[2]+c*X[3]]
hopf=lambda x:[2*(x[0]*x[2]+x[1]*x[3]),2*(x[0]*x[3]-x[1]*x[2]),x[0]**2+x[1]**2-x[2]**2-x[3]**2]
sq=lambda x:sum(z*z for z in x)
assert s.expand(sum(z*z for z in hopf(X))-sq(X)**2)==0
for j in range(3):assert s.expand(hopf(Y)[j]-(c*c+d*d)*hopf(X)[j])==0
assert s.expand(sq(Y)-(c*c+d*d)*sq(X))==0
V=s.symbols('V0:4'); w=[-X[1],X[0],-X[3],X[2]]
t0=sum(w[i]*V[i] for i in range(4))
sos=sum((w[i]*V[j]-w[j]*V[i])**2 for i in range(4) for j in range(i+1,4))
assert s.expand(sq(X)*sq(V)-t0**2-sos)==0
print('PASS: Hopf norm/action and Taub-NUT 6-square positivity certificate')
print('LIMITS: no general metric-to-Ricci Lean or S3/U1 smooth quotient theorem')
