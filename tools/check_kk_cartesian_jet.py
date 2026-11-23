#!/usr/bin/env python3
"""Independent symbolic check of the 5D Cartesian KK inverse and first jet.

This is NOT a Lean calculus proof: the Lean module takes the first
partial metric derivatives as rational jet tables, checked here
against actual derivatives of the metric. SymPy 1.14.0.
Coordinates (t,x,y,z,psi); H=1+a*z, U=a*x; local H>0.
"""
import sympy as s
from itertools import product

t,x,y,z,psi,a=s.symbols("t x y z psi a",real=True)
h=s.symbols("h",positive=True,real=True)
u=s.symbols("u",real=True)
coords=[t,x,y,z,psi]
H=1+a*z
U=a*x

def zero(expr,desc):
    expr=s.factor(s.cancel(s.trigsimp(s.simplify(expr))))
    assert expr==0,(desc,expr)

M=s.diag(-h,h*h,h*h+u*u,h*h,1)
M[2,4]=M[4,2]=u
N=s.diag(-h,1,1,1,h*h+u*u)
N[2,4]=N[4,2]=-u
for i,j in product(range(5),repeat=2):
    zero((M*N)[i,j]-(h*h if i==j else 0),f"scaled matrix inverse {i},{j}")
print("PASS: all 25 polynomial scaled inverse entries")

G=(M/h).subs({h:H,u:U})
I=(N/h).subs({h:H,u:U})
for i,j in product(range(5),repeat=2):
    zero((G*I)[i,j]-(1 if i==j else 0),f"unscaled inverse {i},{j}")
print("PASS: all 25 unscaled metric/inverse entries")

dx=s.zeros(5)
dx[2,2]=2*u*a/h
dx[2,4]=dx[4,2]=a/h
dz=s.zeros(5)
dz[1,1]=dz[3,3]=a
dz[2,2]=a-a*u*u/h**2
dz[2,4]=dz[4,2]=-a*u/h**2
dz[4,4]=-a/h**2
for d,guess,name in [(x,dx,"x"),(z,dz,"z")]:
    guess=guess.subs({h:H,u:U})
    for i,j in product(range(5),repeat=2):
        zero(s.diff(G[i,j],d)-guess[i,j],f"partial_{name} g[{i},{j}]")
for d in (t,y,psi):
    for i,j in product(range(5),repeat=2):
        zero(s.diff(G[i,j],d),f"zero partial_{d} g[{i},{j}]")
print("PASS: all 125 metric first partials equal finite-jet tables")

inv=s.simplify(G.inv())
for i,j in product(range(5),repeat=2):
    zero(inv[i,j]-I[i,j],f"inverse used by connection {i},{j}")
Gam={}
for i,j,k in product(range(5),repeat=3):
    Gam[i,j,k]=s.factor(sum(inv[i,m]*
       (s.diff(G[m,k],coords[j])+s.diff(G[m,j],coords[k])
         -s.diff(G[j,k],coords[m]))
        for m in range(5))/2)
for i,j,k in product(range(5),repeat=3):
    zero(Gam[i,j,k]-Gam[i,k,j],f"torsion free {i},{j},{k}")
expected={
   (3,4,4): a/(2*H**3),
   (1,2,4): -a/(2*H**2),
   (3,2,4): a*U/(2*H**3),
   (3,1,1): -a/(2*H),
   (3,3,3): a/(2*H)
}
for ijk,v in expected.items():
    zero(Gam[ijk]-v,f"Levi-Civita {ijk}")
print("PASS: 125 lower-index connection symmetries + 5 exact components")

RiemXzxz=s.factor(s.diff(Gam[1,3,3],coords[1])
                     -s.diff(Gam[1,1,3],coords[3])
                     +sum(Gam[1,1,m]*Gam[m,3,3]
                          -Gam[1,3,m]*Gam[m,1,3]
                          for m in range(5)))
zero(RiemXzxz-a*a/(2*H**2),"R^x_zxz")
print("PASS: curved metric has R^x_zxz=a²/(2H²)")
print("SCOPE: first metric partials are SymPy, inverse and jet Gamma are Lean")
