#!/usr/bin/env python3
"""Independent local 5D KK/4D EMD radial-ansatz consistency oracle.

Exact, symbolic and entirely independent of primitive-lean source files.
This is NOT a Lean proof of differentiable Lorentzian tensor geometry.

Metric: ds5^2 = -dt^2 + H(r)(dr^2+r^2 dOmega^2)
              + H(r)^(-1)(dpsi+b*cos(theta)*dvarphi)^2.
Domain: r>0, H(r)>0, 0<theta<pi, real constant b.
Riemann sign convention as the existing PR #199.
SymPy required: 1.14.0 (or a compatible version).
"""
from itertools import product
import sympy as S

r = S.symbols("r", positive=True, real=True)
Theta = S.symbols("theta", real=True)
b = S.symbols("b", real=True)
t, az, psi = S.symbols("t az psi", real=True)
H = S.Function("H", positive=True)(r)
Hp, Hpp = S.diff(H,r), S.diff(H,r,2)
coords5 = [t,r,Theta,az,psi]
coords4 = coords5[:4]

def verify_zero(expr, label):
    result = S.factor(S.cancel(S.trigsimp(S.simplify(expr))))
    if result != 0:
        raise AssertionError((label, result))

def ricci_tensor(metric, coords):
    n = len(coords)
    inverse = metric.inv().applyfunc(S.factor)  # Do not copy stored inverse.
    for i,j in product(range(n),repeat=2):
        verify_zero((metric*inverse)[i,j] - int(i==j), f'inverse {i} {j}')
    metric_derivatives = [[[S.diff(metric[j,k],x) for k in range(n)]
                           for j in range(n)] for x in coords]
    connection = {}
    for a in range(n):
        for j in range(n):
            for k in range(j,n):
                z = S.factor(sum(inverse[a,u]*(metric_derivatives[j][u][k]
                        +metric_derivatives[k][u][j]-metric_derivatives[u][j][k])
                        for u in range(n))/2)
                if z != 0:
                    connection[a,j,k] = connection[a,k,j] = z
    tensor = S.zeros(n)
    for a,j in product(range(n),repeat=2):
        tensor[a,j] = S.factor(sum(
          S.diff(connection.get((c,a,j),0),coords[c])
          -S.diff(connection.get((c,a,c),0),coords[j])
          +sum(connection.get((c,a,j),0)*connection.get((u,c,u),0)
          -connection.get((c,a,u),0)*connection.get((u,j,c),0)
          for u in range(n))
          for c in range(n)))
    return tensor, inverse

def check_5d(L,Q):
    A=b*S.cos(Theta)
    G5=S.diag(-1,H,H*r*r,H*r*r*S.sin(Theta)**2+A*A/H,1/H)
    G5[3,4]=G5[4,3]=A/H
    R5, inv5 = ricci_tensor(G5, coords5)
    predicted=S.zeros(5)
    predicted[1,1]=-L/(2*r*H)
    predicted[2,2]=-Q/(2*r*r*H**2)
    predicted[3,3]=-((r*H*S.sin(Theta))**2-(b*S.cos(Theta))**2)*Q/(2*r**4*H**4)
    predicted[3,4]=predicted[4,3]=b*S.cos(Theta)*Q/(2*r**4*H**4)
    predicted[4,4]=Q/(2*r**4*H**4)
    for i,j in product(range(5),repeat=2):
        verify_zero(R5[i,j]-predicted[i,j],f'5D R{i}{j}')
    scalar5=S.factor(S.trace(inv5*R5))
    verify_zero(scalar5+L/(2*r*H**2)+Q/(2*r**4*H**3),'5D scalar')
    # Local KK metric reconstruction, 5D g / 4D g / A / Phi definitions.
    q=S.sqrt(H)
    G4=S.diag(-1/q,q,q*r*r,q*r*r*S.sin(Theta)**2)
    fieldA=[S.S(0),S.S(0),S.S(0),A]
    for i,j in product(range(4),repeat=2):
        verify_zero(G5[i,j] - (q*G4[i,j]+fieldA[i]*fieldA[j]/H),f'metric projection {i},{j}')
    for i in range(4):
        verify_zero(G5[i,4]-fieldA[i]/H,f'metric mixing {i}')
    verify_zero(G5[4,4]-1/H,'metric fibre')
    return R5, scalar5, G4, fieldA

def check_4d(G4,A,R5,L,Q):
    R4,I4=ricci_tensor(G4, coords4)
    phi=S.sqrt(3)*S.log(H)/2
    dphi=[S.diff(phi,x) for x in coords4]
    F=S.Matrix(4,4,lambda i,j:S.diff(A[j],coords4[i])-S.diff(A[i],coords4[j]))
    Fu=I4*F*I4
    F2=S.factor(sum(F[i,j]*Fu[i,j] for i,j in product(range(4),repeat=2)))
    verify_zero(F2-2*b*b/(H*r**4),'F^2')
    E=S.zeros(4)
    for i,j in product(range(4),repeat=2):
        electromag=(sum(F[i,u]*I4[u,v]*F[j,v]
                          for u,v in product(range(4),repeat=2))
                 -G4[i,j]*F2/4)
        rhs=dphi[i]*dphi[j]/2+H**(-S.Rational(3,2))*electromag/2
        E[i,j]=S.factor(R4[i,j]-rhs)
    pred=S.zeros(4)
    pred[0,0]=-Q/(4*r**4*H**3)
    charge_defect=b**2-(r*r*Hp)**2
    pred[1,1]=-(r**3*H*L-charge_defect)/(4*r**4*H**2)
    pred[2,2]=-Q/(4*r*r*H**2)
    pred[3,3]=S.sin(Theta)**2*pred[2,2]
    for i,j in product(range(4),repeat=2):
        verify_zero(E[i,j]-pred[i,j],f'4D Einstein residual {i}{j}')
    sqrt_abs_det=S.sqrt(H)*r*r*S.sin(Theta)  # positive on chart 0<theta<pi
    maxwell=[S.factor(sum(S.diff(sqrt_abs_det*H**(-S.Rational(3,2))*Fu[u,j],coords4[u])
                  for u in range(4))) for j in range(4)]
    for j in range(4):verify_zero(maxwell[j],f'Maxwell {j}')
    wave=S.factor(sum(S.diff(sqrt_abs_det*I4[u,u]*dphi[u],coords4[u])
                for u in range(4))/sqrt_abs_det)
    scalar=S.factor(wave+S.sqrt(3)*H**(-S.Rational(3,2))*F2/4)
    verify_zero(scalar-S.sqrt(3)*Q/(2*r**4*H**S.Rational(5,2)),'dilaton source')
    # Five exact cross-theory residual identities for any smooth positive H.
    verify_zero(E[0,0]+H*R5[4,4]/2,'bridge E_tt')
    verify_zero(E[1,1]-(R5[1,1]+H**2*R5[4,4]/2),'bridge E_rr')
    verify_zero(E[2,2]+r*r*H**2*R5[4,4]/2,'bridge E_theta')
    verify_zero(E[3,3]-S.sin(Theta)**2*E[2,2],'bridge E_phi')
    verify_zero(scalar-S.sqrt(3)*H**S.Rational(3,2)*R5[4,4],'bridge scalar')
    return E, scalar

def check_on_shell_and_off_shell(L,Q,R5,Rscalar5,E,scalar):
    a,c,d=S.symbols('a c d',real=True)
    # On shell: arbitrary normalization c, charge b=+/-a.
    harmonic=c+a/r
    substitutions={H:harmonic,Hp:S.diff(harmonic,r),Hpp:S.diff(harmonic,r,2)}
    for sign in (1,-1):
        case=dict(substitutions,**{})
        case[b]=sign*a
        for i,j in product(range(5),repeat=2):
            verify_zero(R5[i,j].subs(case).doit(),f'on shell 5D {sign} {i},{j}')
        for i,j in product(range(4),repeat=2):
            verify_zero(E[i,j].subs(case).doit(),f'on shell EMD {sign} {i},{j}')
        verify_zero(scalar.subs(case).doit(),f'on shell scalar {sign}')
    # Off shell: a/r^2 correction violates harmonicity independently of b.
    nonharmonic=c+a/r+d/r**2
    case={H:nonharmonic, Hp:S.diff(nonharmonic,r), Hpp:S.diff(nonharmonic,r,2)}
    verify_zero(L.subs(case)-2*d/r**3,'nonharmonic L')
    verify_zero(R5[1,1].subs(case) + d/(r**4*nonharmonic),'nonharmonic Ric_rr')
    # An exact counterexample: scalar-flat does NOT imply Ricci-flat.
    # With H=r^-2 and b=0 the spatial metric is H^2 x S^2,
    # whose scalar curvatures cancel but whose Ricci tensor is nonzero.
    scalar_flat=1/r**2
    case={H:scalar_flat, Hp:S.diff(scalar_flat,r),
          Hpp:S.diff(scalar_flat,r,2), b:S.S(0)}
    verify_zero(Rscalar5.subs(case),'scalar-flat offshell counterexample')
    verify_zero(R5[1,1].subs(case)+1/r**2,'nonzero scalar-flat R_rr')
    verify_zero(R5[4,4].subs(case)+r**2,'nonzero scalar-flat R_psipsi')
    # Polynomial identity plus integration argument: (r^2 H')'=rL.
    verify_zero(S.diff(r*r*Hp,r)-r*L,'harmonic flux derivative')
    verify_zero(Q-(b*b-(r*r*Hp)**2+r**3*H*L),'two-defect decomposition')


def main():
    L=r*Hpp+2*Hp
    Q=b*b-r**4*Hp**2+r**3*H*L
    R5,Rscalar5,G4,A=check_5d(L,Q)
    print('PASS: 25/25 5D Ricci components factor through L,Q; full Ricci scalar')
    E,scalar=check_4d(G4,A,R5,L,Q)
    print('PASS: 16/16 4D EMD Einstein, 4 Maxwell, 1 scalar residual')
    print('PASS: 5 exact identities equating 4D and 5D residuals')
    check_on_shell_and_off_shell(L,Q,R5,Rscalar5,E,scalar)
    print('PASS: H=c+a/r with b=±a; H=c+a/r+d/r² fails when d!=0')
    print('PASS: H=r^-2,b=0 has R5 scalar=0 but R_rr=-r^-2 and R_psipsi=-r²')
    print('PASS: (r² H\')\' = rL, hence local classification with H>0')
    print('SCOPE: full tensors are verified by SymPy, not Lean; no global bundle atlas')

if __name__=='__main__':main()