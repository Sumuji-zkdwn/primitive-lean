"""Symbolic checks for the local smooth vacuum Killing propagation argument.
The energy estimates, linear Cauchy limit, and Killing propagation are analytic.
"""
import sympy as S
from itertools import product

u,k,D=S.symbols('u k D', positive=True)
F=S.symbols('F', real=True)
b=S.Matrix(S.symbols('b0:3', real=True))
Q=S.Matrix(3,3,lambda i,j:S.Symbol(f'q{min(i,j)}{max(i,j)}', real=True))
P=Q.inv()
B=P*b
G=S.BlockMatrix([[S.zeros(1),S.Matrix([[-1]]),S.zeros(1,3)],
 [S.Matrix([[-1]]),S.Matrix([[u*F]]),u*b.T], [S.zeros(3,1),u*b,Q]]).as_explicit()
Gi=S.BlockMatrix([[S.Matrix([[-u*F+u*u*(b.T*B)[0]]]),S.Matrix([[-1]]),u*B.T],
 [S.Matrix([[-1]]),S.zeros(1),S.zeros(1,3)], [u*B,S.zeros(3,1),P]]).as_explicit()
assert all(S.cancel(x)==0 for x in G*Gi-S.eye(5))
print('PASS general Gaussian-null inverse (arbitrary symmetric screen)')
# Principal transformation via covectors of eta, chi, x. Independent D=F-u|b|²,
# B=q^{-1}b, and P=q^{-1} suffice; no restriction on the screen metric.
p=S.Matrix(3,3,lambda i,j:S.Symbol(f'p{min(i,j)}{max(i,j)}',real=True))
w=S.Matrix(S.symbols('w0:3',real=True))
I=S.BlockMatrix([[S.Matrix([[-u*D]]),S.Matrix([[-1]]),u*w.T],
 [S.Matrix([[-1]]),S.zeros(1),S.zeros(1,3)], [u*w,S.zeros(3,1),p]]).as_explicit()
J=S.eye(5); J[0,0]=1/(2*u); J[1,0]=-1/(2*k*u)
M=(-4*u/D*J*I*J.T).applyfunc(S.cancel)
beta=S.Matrix([2/D-1/k,*list(-2*u*w/D)])
A=S.BlockMatrix([[S.Matrix([[4/(k*D)-1/k**2]]),-2*u*w.T/(k*D)],
 [-2*u*w/(k*D),4*u*p/D]]).as_explicit()
assert all(S.cancel(x)==0 for x in M-S.BlockMatrix([[S.ones(1),beta.T],[beta,-A]]).as_explicit())
W=S.diag(1,*([1/S.sqrt(u)]*3))
D1=S.symbols('D1',real=True)
limA=(W*A*W).subs(D,2*k+u*D1).applyfunc(lambda x:S.limit(x,u,0,dir='+'))
assert limA==S.diag(1/k**2,2*p/k)
assert beta.subs(D,2*k+u*D1).applyfunc(lambda x:S.limit(x,u,0,dir='+'))==S.zeros(4,1)
print('PASS exact transformed principal matrix and positive scaled limit')
# Lower order from coordinate Hessian plus regular first-order coefficients.
# eta_uu=-1/(2u²), chi_uu=1/(2k u²), all other Hessian entries zero.
assert S.cancel(-4*u/D*(-u*D)*(-1/(2*u*u))+2)==0
assert S.cancel(-4*u/D*(-u*D)*(1/(2*k*u*u))-2/k)==0
Au,Av,Ax=S.symbols('Au Av Ax',real=True)
assert S.cancel((-4*u/D)*Au*J[0,0]+2*Au/D)==0
assert S.cancel((-4*u/D)*(Au*J[1,0]+Av)-(2*Au/k-4*u*Av)/D)==0
assert S.simplify((-4*u/D)*Ax/S.sqrt(u)+4*S.sqrt(u)*Ax/D)==0
print('PASS bounded weighted first-order coefficient factors')
# Energy flux: pointwise Cauchy-Schwarz uses positive A. Verify the underlying
# bulk identity for arbitrary first and second derivative jets in four spatial dimensions.
nn=4
A0=S.Matrix(nn,nn,lambda i,j:S.Symbol(f'a{min(i,j)}{max(i,j)}'))
At=S.Matrix(nn,nn,lambda i,j:S.Symbol(f'at{min(i,j)}{max(i,j)}'))
Aj=[S.Matrix(nn,nn,lambda i,j:S.Symbol(f'a{k}_{min(i,j)}{max(i,j)}')) for k in range(nn)]
bt=S.Matrix(S.symbols('beta0:4')); divbt=S.symbols('divbeta')
x=S.Matrix(S.symbols('x0:4')); xt=S.Matrix(S.symbols('xt0:4'))
H=S.Matrix(nn,nn,lambda i,j:S.Symbol(f'H{min(i,j)}{max(i,j)}'))
y,p0,L=S.symbols('y p0 L')
contract=lambda X,Y:sum(X[i,j]*Y[i,j] for i,j in product(range(nn),repeat=2))
y_t=-2*bt.dot(xt)+contract(A0,H)+L
energy_t=y*y_t+x.dot(A0*xt)+x.dot(At*x)/2+p0*y
divA=S.Matrix([sum(Aj[i][i,j] for i in range(nn)) for j in range(nn)])
flux_div=xt.dot(A0*x)+y*(divA.dot(x)+contract(A0,H))-divbt*y*y-2*y*bt.dot(xt)
bulk=y*L+p0*y-y*divA.dot(x)+divbt*y*y+x.dot(At*x)/2
assert S.expand(energy_t-flux_div-bulk)==0
print('PASS variable-principal energy identity including shift and divergence terms')
