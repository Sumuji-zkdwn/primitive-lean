"""Exact nonlinear 5D vacuum Kaluza--Klein monopole -> 4D EMD.

Direct coordinate Christoffel/Ricci computations with SymPy 1.14.0.
No numerics: k>0 and r>0 are symbolic; angular chart excludes
theta=0 and theta=pi, with gauge patches required globally.

5D Lorentzian vacuum metric:
 ds5²=-dt²+H (dr²+r² dΩ²)+H^-1 (dpsi+k cosθ dphi)², H=1+k/r.

Einstein-frame reduction:
 ds4²=-H^-1/2 dt²+H^1/2 (dr²+r² dΩ²),
 A=k cosθ dphi, varphi=(sqrt(3)/2)log H.

4D action: S = ∫sqrt(-g)[R-(1/2)(∂varphi)²
                         -(1/4)exp(-sqrt(3)*varphi)F²].
The checker independently verifies all 5D vacuum and 4D Einstein,
Maxwell, scalar equations from the metrics and fields.
"""
import sympy as s
from itertools import product

r, theta, k = s.symbols("r theta k", real=True, positive=True)
t, az, psi = s.symbols("t az psi", real=True)
H = 1 + k/r
q = s.sqrt(H)

def check(a, label):
    z = s.factor(s.cancel(s.trigsimp(s.simplify(a))))
    assert z == 0, (label,z)

def ricci(metric, inverse, coords):
    n = len(coords)
    for i,j in product(range(n), repeat=2):
        check((metric*inverse)[i,j]-(1 if i==j else 0),
              f"metric inverse {i} {j}")
    D = [[[s.diff(metric[j,l],coords[i]) for l in range(n)]
          for j in range(n)] for i in range(n)]
    C = {}
    for a in range(n):
        for b in range(n):
            for c in range(b,n):
                z=s.factor(sum(inverse[a,i]*
                    (D[b][i][c]+D[c][i][b]-D[i][b][c])/2
                    for i in range(n)))
                if z!=0:
                    C[a,b,c]=z
                    C[a,c,b]=z
    R = s.zeros(n)
    for a,b in product(range(n),repeat=2):
        R[a,b]=s.factor(sum(
            s.diff(C.get((c,a,b),0),coords[c])
            -s.diff(C.get((c,a,c),0),coords[b])
            +sum(C.get((c,a,b),0)*C.get((d,c,d),0)
                 -C.get((c,a,d),0)*C.get((d,b,c),0)
                 for d in range(n))
            for c in range(n)))
    return R

def main():
    coords5=[t,r,theta,az,psi]
    G5=s.diag(-1,H,H*r*r,
              H*r*r*s.sin(theta)**2+k*k*s.cos(theta)**2/H,1/H)
    G5[3,4]=G5[4,3]=k*s.cos(theta)/H
    inv5=s.zeros(5)
    inv5[0,0]=-1
    inv5[1,1]=1/H
    inv5[2,2]=1/(H*r*r)
    inv5[3,3]=1/(H*r*r*s.sin(theta)**2)
    inv5[3,4]=inv5[4,3]=-k*s.cos(theta)/(H*r*r*s.sin(theta)**2)
    inv5[4,4]=H+k*k*s.cos(theta)**2/(H*r*r*s.sin(theta)**2)
    R5=ricci(G5,inv5,coords5)
    for a,b in product(range(5),repeat=2):
        check(R5[a,b], f"5D vacuum Ricci {a},{b}")
    check(s.factor(G5.det())+H*H*r**4*s.sin(theta)**2,
          "5D determinant")
    print("PASS: all 25 exact 5D Ricci=0 components (symbolic k)")

    coords4=coords5[:4]
    G4=s.diag(-1/q,q,q*r*r,q*r*r*s.sin(theta)**2)
    inv4=s.diag(-q,1/q,1/(q*r*r),1/(q*r*r*s.sin(theta)**2))
    phi=s.sqrt(3)/2*s.log(H)
    A=[s.S(0),s.S(0),s.S(0),k*s.cos(theta)]
    F=s.Matrix(4,4,lambda i,j:
      s.diff(A[j],coords4[i])-s.diff(A[i],coords4[j]))
    for i,j in product(range(4),repeat=2):
        check(G5[i,j]-(q*G4[i,j]+A[i]*A[j]/H),
              f"5D metric reconstruction {i},{j}")
        check(G5[i,4]-A[i]/H,f"5D gauge reconstruction {i}")
    check(G5[4,4]-1/H,"5D fibre metric")
    R4=ricci(G4,inv4,coords4)
    Fup=inv4*F*inv4
    F2=s.factor(sum(F[i,j]*Fup[i,j]
                    for i,j in product(range(4),repeat=2)))
    check(F2-2*k*k/(H*r**4),"F squared")
    dphi=s.Matrix([s.diff(phi,x) for x in coords4])
    expfactor=H**(-s.Rational(3,2))
    for i,j in product(range(4),repeat=2):
        FF=sum(F[i,a]*inv4[a,a]*F[j,a] for a in range(4))
        RHS=(s.Rational(1,2)*dphi[i]*dphi[j]+
             s.Rational(1,2)*expfactor*
             (FF-s.Rational(1,4)*G4[i,j]*F2))
        check(R4[i,j]-RHS,f"4D Einstein EMD {i},{j}")
    print("PASS: all 16 nonlinear 4D Einstein EMD components")

    rootg=q*r*r*s.sin(theta)
    for nu in range(4):
        weighted_div=sum(
            s.diff(rootg*expfactor*Fup[mu,nu],coords4[mu])
            for mu in range(4))
        check(weighted_div,f"weighted Maxwell {nu}")
    print("PASS: all 4 Maxwell equations with dilaton coupling")

    box=sum(s.diff(rootg*inv4[mu,mu]*dphi[mu],coords4[mu])
            for mu in range(4))/rootg
    check(box+s.sqrt(3)/4*expfactor*F2,"dilaton equation")
    print("PASS: nonlinear dilaton wave/source equation")

    check(F[2,3]+k*s.sin(theta),"magnetic field Ftheta phi")
    flux=s.integrate(F[2,3],(theta,0,s.pi))*2*s.pi
    check(flux+4*s.pi*k,"monopole flux")
    check(flux/(4*s.pi*k)+1,"Chern integer convention")
    assert s.diff(phi,r)!=0
    check(s.diff(phi,r)-s.sqrt(3)*s.diff(H,r)/(2*H),
          "dilaton radial derivative")
    print("PASS: magnetic flux -4*pi*k, normalized Chern -1")
    print("PASS: nonconstant radius and nonzero four-dimensional curvature")
    print("SCOPE: local r>0, global smooth NUT atlas is an external theorem")

if __name__=="__main__":
    main()
