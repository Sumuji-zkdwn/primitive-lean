#!/usr/bin/env python3
"""Independent exact non-radial Cartesian GH / 4D EMD witness.

H=1+a*z; A=a*x*dy, on the local patch H>0. Pure 5D vacuum, symbolic a.
This is not an atlas or a general Gibbons-Hawking formal proof.
SymPy 1.14.0.
"""
import sympy as s
from itertools import product

t,x,y,z,psi=s.symbols('t x y z psi',real=True)
a=s.symbols('a',real=True)
c5=[t,x,y,z,psi]
c4=c5[:4]
H=1+a*z

def zero(expr,label):
    expr=s.factor(s.cancel(s.trigsimp(s.simplify(expr))))
    assert expr==0,(label,expr)

def geometry(metric,coords):
    n=len(coords)
    inv=metric.inv().applyfunc(s.factor)
    for i,j in product(range(n),repeat=2):
        zero((metric*inv)[i,j]-int(i==j),f'inverse {i},{j}')
    D=[[[s.diff(metric[j,k],coords[i]) for k in range(n)]
         for j in range(n)] for i in range(n)]
    G={}
    for i,j,k in product(range(n),repeat=3):
        val=s.factor(sum(inv[i,m]*(D[j][m][k]+D[k][m][j]-D[m][j][k])
                         for m in range(n))/2)
        if val!=0:G[i,j,k]=val
    R=s.zeros(n)
    for i,j in product(range(n),repeat=2):
        R[i,j]=s.factor(sum(
            s.diff(G.get((k,i,j),0),coords[k])
            -s.diff(G.get((k,i,k),0),coords[j])
            +sum(G.get((k,i,j),0)*G.get((l,k,l),0)
                 -G.get((k,i,l),0)*G.get((l,j,k),0)
                 for l in range(n))
            for k in range(n)))
    return R,inv,G

A=[s.S(0),s.S(0),a*x,s.S(0)]
G5=s.diag(-1,H,H+a*a*x*x/H,H,1/H)
G5[2,4]=G5[4,2]=a*x/H
R5,I5,Gam5=geometry(G5,c5)
for i,j in product(range(5),repeat=2):
    zero(R5[i,j],f'5D Ricci {i},{j}')
# R^x_{z x z} is nonzero when a!=0.
ri=s.factor(s.diff(Gam5.get((1,3,3),0),x)
       -s.diff(Gam5.get((1,1,3),0),z)
       +sum(Gam5.get((1,1,m),0)*Gam5.get((m,3,3),0)
            -Gam5.get((1,3,m),0)*Gam5.get((m,1,3),0)
            for m in range(5)))
zero(ri-a*a/(2*H**2),'Riemann not flat')
print('PASS: all 25 nonradial 5D Ricci components zero; Riemann nonzero')

G4=s.diag(-H**(-s.Rational(1,2)),H**s.Rational(1,2),
          H**s.Rational(1,2),H**s.Rational(1,2))
R4,I4,_=geometry(G4,c4)
for i,j in product(range(4),repeat=2):
    zero(G5[i,j]-s.sqrt(H)*G4[i,j]-A[i]*A[j]/H,'metric reduction')
    zero(G5[i,4]-A[i]/H,'gauge extraction')
phi=s.sqrt(3)*s.log(H)/2
dphi=s.Matrix([s.diff(phi,q) for q in c4])
F=s.Matrix(4,4,lambda i,j:s.diff(A[j],c4[i])-s.diff(A[i],c4[j]))
Fu=I4*F*I4
F2=s.factor(sum(F[i,j]*Fu[i,j] for i,j in product(range(4),repeat=2)))
zero(F2-2*a*a/H,'F squared')
for i,j in product(range(4),repeat=2):
    ff=sum(F[i,m]*I4[m,n]*F[j,n] for m,n in product(range(4),repeat=2))
    rhs=dphi[i]*dphi[j]/2+H**(-s.Rational(3,2))*(ff-G4[i,j]*F2/4)/2
    zero(R4[i,j]-rhs,f'4D Einstein EMD {i},{j}')
print('PASS: all 16 nonlinear 4D EMD Einstein residuals zero')

rootg=s.sqrt(H)
for nu in range(4):
    div=sum(s.diff(rootg*H**(-s.Rational(3,2))*Fu[mu,nu],c4[mu])
            for mu in range(4))
    zero(div,f'weighted Maxwell {nu}')
wave=sum(s.diff(rootg*I4[mu,mu]*dphi[mu],c4[mu])
         for mu in range(4))/rootg
zero(wave+s.sqrt(3)*H**(-s.Rational(3,2))*F2/4,'dilaton equation')
print('PASS: all 4 weighted Maxwell equations and nonlinear dilaton equation')
print('SCOPE: H>0 local patch; no global circle atlas or generic geometry formalization')


# Additional NONAFFINE harmonic example: Hq=1+a*x*y, Aq=a*(y^2-x^2)*dz/2.
# Hq has d_x d_y Hq=a!=0, so this is not an affine-harmonic witness.
Hq=1+a*x*y
Aq=s.Rational(1,2)*a*(y*y-x*x)
G5q=s.diag(-1,Hq,Hq,Hq+Aq*Aq/Hq,1/Hq)
G5q[3,4]=G5q[4,3]=Aq/Hq
R5q,I5q,_=geometry(G5q,c5)
for i,j in product(range(5),repeat=2):
    zero(R5q[i,j],f'nonaffine 5D Ricci {i},{j}')
G4q=s.diag(-Hq**(-s.Rational(1,2)),Hq**s.Rational(1,2),
           Hq**s.Rational(1,2),Hq**s.Rational(1,2))
Rq,Invq,_=geometry(G4q,c4)
Avec=[s.S(0),s.S(0),s.S(0),Aq]
Ph=s.sqrt(3)*s.log(Hq)/2
Dph=s.Matrix([s.diff(Ph,u) for u in c4])
Fq=s.Matrix(4,4,lambda i,j:s.diff(Avec[j],c4[i])-s.diff(Avec[i],c4[j]))
Fqu=Invq*Fq*Invq
Fq2=s.factor(sum(Fq[i,j]*Fqu[i,j] for i,j in product(range(4),repeat=2)))
for i,j in product(range(4),repeat=2):
    ff=sum(Fq[i,k]*Invq[k,l]*Fq[j,l] for k,l in product(range(4),repeat=2))
    rhs=Dph[i]*Dph[j]/2+Hq**(-s.Rational(3,2))*(ff-G4q[i,j]*Fq2/4)/2
    zero(Rq[i,j]-rhs,f'nonaffine 4D EMD {i},{j}')
rootgq=s.sqrt(Hq)
for nu in range(4):
    div=sum(s.diff(rootgq*Hq**(-s.Rational(3,2))*Fqu[mu,nu],c4[mu])
            for mu in range(4))
    zero(div,f'nonaffine weighted Maxwell {nu}')
waveq=sum(s.diff(rootgq*Invq[mu,mu]*Dph[mu],c4[mu]) for mu in range(4))/rootgq
zero(waveq+s.sqrt(3)*Hq**(-s.Rational(3,2))*Fq2/4,'nonaffine scalar')
zero(s.diff(Hq,x,y)-a,'nonzero harmonic-potential Hessian')
zero(s.diff(Hq,x,x)+s.diff(Hq,y,y)+s.diff(Hq,z,z),'harmonic Hq')
print('PASS: nonaffine H=1+a*x*y: 25 Ricci, 16 EMD Einstein, 4 Maxwell, scalar')
