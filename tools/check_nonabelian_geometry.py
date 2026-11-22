"""Finite gauge-covariant KK scaffold and exact so(3) connection checks.

Source-free gravitational Yang--Mills dynamics is NOT derived. Standard Python
and SymPy only, using exact integer/rational arithmetic.
"""
from itertools import permutations, product
from collections import deque, Counter
import sympy as S

E = (0,1,2)
PERMS = tuple(permutations(E))

def mul(p,q):
    return tuple(p[q[i]] for i in E)

def inv(p):
    return tuple(p.index(i) for i in E)

def order(p):
    a=E
    for n in range(1,7):
        a=mul(p,a)
        if a==E:
            return n
    raise AssertionError(p)

s=(1,0,2)
t=(0,2,1)
assert mul(s,t)!=mul(t,s)
assert order(mul(s,t))==3

def edges_from_triplet(vals):
    """U_{01}, U_{12}, U_{20}; reverse edges are inverses."""
    U={(0,1):vals[0],(1,2):vals[1],(2,0):vals[2]}
    U.update({(b,a):inv(p) for (a,b),p in list(U.items())})
    return U

def gauge(U,h):
    return {(i,j):mul(mul(h[j],u),inv(h[i])) for (i,j),u in U.items()}

def holonomy(U):
    return mul(U[2,0],mul(U[1,2],U[0,1]))

def lifted_neighbours(U,node):
    i,g=node
    for j in E:
        if i!=j:
            yield j,mul(U[i,j],g)
    for generator in (s,t):
        yield i,mul(g,generator)

def relabel(node,h):
    i,g=node
    return i,mul(h[i],g)

def distance_hist(U):
    vertices=tuple((i,g) for i in E for g in PERMS)
    hist=Counter()
    for start in vertices:
        q=deque([start])
        d={start:0}
        while q:
            x=q.popleft()
            for y in lifted_neighbours(U,x):
                if y not in d:
                    d[y]=d[x]+1
                    q.append(y)
        assert len(d)==len(vertices)
        for v in vertices:
            hist[d[v]]+=1
    return hist

def check_group():
    for a,b,c in product(PERMS,repeat=3):
        assert mul(mul(a,b),c)==mul(a,mul(b,c))
        assert mul(a,inv(a))==E
    Uflat=edges_from_triplet((E,E,E))
    Utwist=edges_from_triplet((s,t,E))
    assert order(holonomy(Uflat))==1
    assert order(holonomy(Utwist))==3
    assert distance_hist(Uflat)!=distance_hist(Utwist)
    n=0
    # Exhaustive gauge covariance over 216 link triplets x 216 local gauges.
    for links in product(PERMS,repeat=3):
        U=edges_from_triplet(links)
        H=holonomy(U)
        for h in product(PERMS,repeat=3):
            V=gauge(U,h)
            assert holonomy(V)==mul(mul(h[0],H),inv(h[0]))
            for i in E:
                for g in PERMS:
                    a=(i,g)
                    neighbors0={relabel(v,h) for v in lifted_neighbours(U,a)}
                    neighbors1=set(lifted_neighbours(V,relabel(a,h)))
                    assert neighbors0==neighbors1
            n+=1
    print('PASS exact group gauge check:',n,'connections x local gauges')
    print('flat lifted distance histogram:',dict(sorted(distance_hist(Uflat).items())))
    print('twisted lifted distance histogram:',dict(sorted(distance_hist(Utwist).items())))

def check_so3():
    T1=S.Matrix([[0,0,0],[0,0,-1],[0,1,0]])
    T2=S.Matrix([[0,0,1],[0,0,0],[-1,0,0]])
    T3=S.Matrix([[0,-1,0],[1,0,0],[0,0,0]])
    def comm(A,B):return A*B-B*A
    assert comm(T1,T2)==T3 and comm(T2,T3)==T1 and comm(T3,T1)==T2
    a,b,x=S.symbols('a b x',real=True)
    A_x=a*T1; A_y=b*T2
    F=comm(A_x,A_y)
    assert F==a*b*T3
    # Rational stereographic rotation about third axis: gauge h(x).
    c=(1-x*x)/(1+x*x)
    si=2*x/(1+x*x)
    h=S.Matrix([[c,-si,0],[si,c,0],[0,0,1]])
    h_inv=h.T
    assert (h*h_inv-S.eye(3)).applyfunc(S.factor)==S.zeros(3)
    Axp=h*A_x*h_inv-h.diff(x)*h_inv
    Ayp=h*A_y*h_inv
    Fp=(Ayp.diff(x)+comm(Axp,Ayp)).applyfunc(S.factor)
    expected=(h*F*h_inv).applyfunc(S.factor)
    assert (Fp-expected).applyfunc(S.factor)==S.zeros(3)
    # Curvature is gauge covariant, so its invariant magnitude is unchanged.
    assert S.factor(S.trace(F*F))==-2*a*a*b*b
    assert S.factor(S.trace(Fp*Fp)+2*a*a*b*b)==0
    # Gauge-frame change for the metric fibre one-form, using an arbitrary X.
    W=S.symbols('w1')*T1+S.symbols('w2')*T2+S.symbols('w3')*T3
    omega_prime=h_inv*W*h+h_inv*h.diff(x)
    A_prime=h_inv*A_x*h-h_inv*h.diff(x)
    # The dh terms cancel in omega + A.
    B_prime=omega_prime+A_prime
    B_expected=h_inv*(W+A_x)*h
    assert (B_prime-B_expected).applyfunc(S.factor)==S.zeros(3)
    assert S.factor(S.trace(B_prime.T*B_prime-B_expected.T*B_expected))==0
    print('PASS exact so(3) non-Abelian F=[A_x,A_y] and rational gauge covariance')

if __name__=='__main__':
    check_group()
    check_so3()
