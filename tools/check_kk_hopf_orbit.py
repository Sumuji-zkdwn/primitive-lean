#!/usr/bin/env python3
"""Independent exact polynomial checks for Hopf orbit completeness.
No numerical sampling. This is not a kernel or topology proof."""
import sympy as s

a,b,c,d,e,f,g,h=s.symbols("a b c d e f g h",real=True)
N=a*a+b*b
M=e*e+f*f
hx=a*c+b*d-e*g-f*h
hy=a*d-b*c-e*h+f*g
C=a*e+b*f
S=a*f-b*e

assert s.expand(C*a-S*b-N*e)==0
assert s.expand(S*a+C*b-N*f)==0
assert s.expand(C*c-S*d-N*g-(e*hx-f*hy+(M-N)*g))==0
assert s.expand(S*c+C*d-N*h-(f*hx+e*hy+(M-N)*h))==0
assert s.expand(C*C+S*S-N*N-N*(M-N))==0
print("PASS: five exact polynomial phase-reconstruction identities")

u,v=s.symbols("u v",real=True)
X=[a,b,c,d]
Y=[u*a-v*b,v*a+u*b,u*c-v*d,v*c+u*d]
def Hopf(X):
    x0,x1,x2,x3=X
    return [2*(x0*x2+x1*x3),2*(x0*x3-x1*x2),
            x0*x0+x1*x1-x2*x2-x3*x3]
def radius(X):return sum(z*z for z in X)
for p,q in zip(Hopf(Y),Hopf(X)):
    assert s.expand(p-(u*u+v*v)*q)==0
assert s.expand(radius(Y)-(u*u+v*v)*radius(X))==0
print("PASS: Hopf orbit invariance and radius identity")

# Independent dot-product test for the freeness certificate.
W=[s.symbols("w0"),s.symbols("w1"),s.symbols("w2"),s.symbols("w3")]
dot=lambda v,w: sum(x*y for x,y in zip(v,w))
assert s.expand(dot(X,Y)-u*radius(X))==0
RW=[u*W[0]-v*W[1],v*W[0]+u*W[1],u*W[2]-v*W[3],v*W[2]+u*W[3]]
assert s.expand(dot(Y,RW)-(u*u+v*v)*dot(X,W))==0
print("PASS: dot-product preservation, free S1 action on radius-one points")

print("LIMIT: algebraic fibres and freeness; smooth quotient/atlas still not in Lean")
