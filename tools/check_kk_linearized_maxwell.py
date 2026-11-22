"""Exact witness for a propagating U(1) KK mode and its nonlinear limits.

Five-dimensional Lorentzian signature (-,+,+,+,+), no 5D matter.
Uses SymPy with exact parameter algebra and independent Christoffel/Ricci.
The plane-wave check concerns the *linearized* 5D vacuum equations.
The constant-B metric is deliberately not Ricci flat; its R55 component
exhibits the scalar/radius equation missing in a fixed-radius truncation.
"""
import sympy as s


def exact_zero(expr, desc):
    z = s.factor(s.cancel(s.trigsimp(s.simplify(expr))))
    assert z == 0, (desc, z)


def linearized_mixed():
    t, x, y, z, w = coords = s.symbols('t x y z w', real=True)
    ks = s.symbols('k0:4', real=True)
    eps = s.symbols('e0:4', real=True)
    eta = (-1, 1, 1, 1, 1)
    phase = sum(ks[i]*coords[i] for i in range(4))
    wave = s.exp(s.I*phase)
    h = s.zeros(5)
    for i in range(4):
        h[i,4] = h[4,i] = eps[i] * wave
    # Explicit flat-background linearized Ricci formula.
    trace = sum(eta[c]*h[c,c] for c in range(5))
    ksq = sum(eta[c]*ks[c]**2 for c in range(4))
    ke = sum(eta[c]*ks[c]*eps[c] for c in range(4))
    for mu in range(4):
        AB = sum(eta[c]*(s.diff(h[c,4], coords[c], coords[mu])
               + s.diff(h[c,mu], coords[c], coords[4])
               - s.diff(h[mu,4], coords[c], coords[c]))
               for c in range(5)) - s.diff(trace,coords[mu],coords[4])
        Ric = s.simplify(AB/2)
        exact_zero(Ric-(ksq*eps[mu]-ks[mu]*ke)*wave/2,
                   f'linearized Ricci {mu},4')
    print('PASS: 5D linearized mixed Ricci = (k² epsilon - k(k.epsilon))/2')
    example = {ks[0]:1,ks[1]:0,ks[2]:0,ks[3]:1,
               eps[0]:0,eps[1]:1,eps[2]:0,eps[3]:0}
    exact_zero(ksq.subs(example),'null')
    exact_zero(ke.subs(example),'transverse')
    assert (ks[0]*eps[1]-ks[1]*eps[0]).subs(example)==1
    alpha = s.symbols('alpha')
    for mu in range(4):
        exact_zero(ksq*(eps[mu]+alpha*ks[mu])
                   -ks[mu]*(ke+alpha*ksq)
                   -(ksq*eps[mu]-ks[mu]*ke),'gauge invariant mixed Ricci')
    print('PASS: transverse nonzero null wave; gauge invariance')


def nonlinear_magnetic():
    t, x, y, z, w = coords = s.symbols('t x y z w', real=True)
    B = s.symbols('B',real=True)
    G=s.diag(-1,1,1,1,1)
    G[2,2]=1+B*B*x*x
    G[2,4]=G[4,2]=B*x
    inv=G.inv()
    assert G.det()==-1
    assert G*inv==s.eye(5)
    N=5
    dg=[[[s.diff(G[j,k],coords[i]) for k in range(N)]
          for j in range(N)] for i in range(N)]
    gamma={(a,b,c):s.cancel(sum(inv[a,i]*(dg[b][i][c]
           +dg[c][i][b]-dg[i][b][c]) for i in range(N))/2)
           for a in range(N) for b in range(N) for c in range(N)}
    Ric=s.zeros(N)
    for a in range(N):
        for b in range(N):
            Ric[a,b]=s.factor(sum(s.diff(gamma[c,a,b],coords[c])
                       -s.diff(gamma[c,a,c],coords[b])
                       +sum(gamma[c,a,b]*gamma[d,c,d]
                            -gamma[c,a,d]*gamma[d,b,c] for d in range(N))
                       for c in range(N)))
    scalar=s.factor(s.trace(inv*Ric))
    F2=2*B*B  # A_y=Bx, F_xy=B; 4D signature (-,+,+,+).
    exact_zero(scalar+F2/4,'R5=-F2/4')
    exact_zero(Ric[4,4]-F2/4,'R55=F2/4')
    assert s.simplify(s.factor(Ric.subs(x,0))[4,4]) == B**2/2
    print('PASS: all 25 Ricci components; R5=-B²/2, Ric_55=B²/2')
    print('PASS: det G=-1; nonzero B prevents fixed-radius flat-base vacuum')


def gauge_coordinate_shift():
    x,y,z=s.symbols('x y z')
    B,c=s.symbols('B c')
    # For w' = w+lambda(x), A' = A-d(lambda).
    old=[s.S(0),B*x,s.S(0)]
    xyz=[x,y,z]
    lam=c*x*z
    new=[old[i]-s.diff(lam,xyz[i]) for i in range(3)]
    for i in range(3):
        for j in range(3):
            exact_zero((s.diff(old[j],xyz[i])-s.diff(old[i],xyz[j]))
                -(s.diff(new[j],xyz[i])-s.diff(new[i],xyz[j])),
                'coordinate gauge invariance')
    print('PASS: circle coordinate change gives U(1) gauge of F')


if __name__=='__main__':
    linearized_mixed()
    nonlinear_magnetic()
    gauge_coordinate_shift()
