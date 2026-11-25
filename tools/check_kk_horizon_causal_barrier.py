"""Exact local algebra for causal reach of the attached vacuum collar.
Global causal and quotient arguments are proved separately in the note.
"""
import sympy as S

r,s,z=S.symbols('r s z', positive=True)
R,V,X,Y,Z=S.symbols('R V X Y Z', real=True)
f=1-s**2/r**2
u=r-s
A=(r+s)/(2*r**2)
g=S.Matrix([[0,-1,0,0,0],[-1,f,0,0,0],[0,0,r**2/z**2,0,0],[0,0,0,r**2/z**2,0],[0,0,0,0,r**2/z**2]])
vec=S.Matrix([R,V,X,Y,Z]); W=S.Matrix([1,1,0,0,0]); ell=S.Matrix([1,0,0,0,0]); k=S.Matrix([0,1,0,0,0])
norm=lambda v:S.expand((v.T*g*v)[0])
dot=lambda a,b:S.expand((a.T*g*b)[0])
assert S.simplify(f-2*A*u)==0
assert norm(ell)==0 and dot(W,ell)==-1
assert dot(ell,vec)==-V
assert S.simplify(norm(W)+1+s**2/r**2)==0
assert S.simplify(norm(vec)+2*V*(R-A*u*V)-r**2*(X**2+Y**2+Z**2)/z**2)==0
assert S.simplify(norm(vec).subs(r,s)+2*R*V-s**2*(X**2+Y**2+Z**2)/z**2)==0
print('PASS cone inequality, horizon factorization, and future null generator')
# Radial timelike path tangent W; increasing r crosses from inside to outside.
assert S.simplify(dot(W,k)-(f-1))==0
assert norm(k)==f
assert S.simplify(norm(k).subs(r,s))==0
print('PASS timelike crossing and periodic Killing orbit norm')
# With v as parameter, any fixed compact transverse/r path slowed by N
# gives a future timelike curve for sufficiently large N.
N=S.symbols('N', positive=True)
slow=S.Matrix([R/N,1,X/N,Y/N,Z/N])
assert S.simplify(norm(slow)-(f-2*R/N+r**2*(X**2+Y**2+Z**2)/(z**2*N**2)))==0
assert S.simplify(S.limit(norm(slow),N,S.oo)-f)==0
assert S.simplify(S.limit(dot(W,slow),N,S.oo)-(f-1))==0
print('PASS slow paths in chronology-violating collar')
# Opposite circle charts v_+=chi+r*, v_-=-chi+r*, both give the same EF metric.
rs=r+s*S.log((r-s)/(r+s))/2
assert S.simplify(S.diff(rs,r)-1/f)==0
assert S.limit(rs,r,s,dir='+')==-S.oo
# Pullback from diagonal exterior for either sign of dchi.
chi2=S.symbols('chi_dot', real=True)
for sign in [-1,1]:
    vp=sign*chi2+R/f
    assert S.simplify(-2*R*vp+f*vp**2-(-R**2/f+f*chi2**2))==0
print('PASS opposite horizon charts and unbounded relative phase')
print('LIMIT: no operational matter model, no global arrow-of-time theorem, no proof of genericity')
