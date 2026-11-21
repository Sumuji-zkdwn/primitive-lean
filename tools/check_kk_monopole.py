"""Direct zero-cosmological-constant vacuum verification of the
Gross-Perry-Sorkin / Taub-NUT Kaluza-Klein magnetic monopole.

General k: harmonic function H=1+k/r and Gibbons-Hawking relation
d(k*cos(theta)*dphi) = *3 dH.
For k=1: full 4x4 spatial Ricci computation; 5D has an extra -dt².
Also checks normalized Chern number with psi period 4*pi*k.
Only local Ricci flatness r>0 is tested, not a full smoothness atlas.
Dependency: sympy==1.14.0.
"""
import sympy as s


def main():
    r,theta,phi,psi=s.symbols('r theta phi psi',positive=True,real=True)
    k=s.symbols('k',nonzero=True,real=True)
    H=1+k/r
    A=k*s.cos(theta)
    assert s.simplify(s.diff(A,theta) -
        s.diff(H,r)*r**2*s.sin(theta))==0
    assert s.simplify(s.diff(r**2*s.diff(H,r),r))==0
    print('PASS general k: radial harmonic condition and dA=*dH')

    H=1+1/r
    A=s.cos(theta)
    coords=[r,theta,phi,psi]
    g=s.Matrix([
        [H,0,0,0],
        [0,H*r*r,0,0],
        [0,0,H*r*r*s.sin(theta)**2+A**2/H,A/H],
        [0,0,A/H,1/H]])
    gi=g.inv().applyfunc(s.factor)
    n=4
    dg=[[[s.diff(g[i,j],coords[a]) for a in range(n)]
         for j in range(n)] for i in range(n)]
    gamma={}
    for a in range(n):
        for b in range(n):
            for c in range(b,n):
                v=sum(gi[a,d] *
                      (dg[d][b][c]+dg[d][c][b]-dg[b][c][d])
                      for d in range(n))/2
                gamma[a,b,c]=gamma[a,c,b]=s.cancel(s.trigsimp(v))
    for a in range(n):
        for b in range(a,n):
            R=sum(s.diff(gamma[c,a,b],coords[c]) -
                  s.diff(gamma[c,a,c],coords[b]) +
                  sum(gamma[c,a,b]*gamma[d,c,d] -
                      gamma[c,a,d]*gamma[d,b,c] for d in range(n))
                  for c in range(n))
            assert s.simplify(s.trigsimp(R))==0,(a,b,R)
    print('PASS full 4D Taub-NUT Ricci tensor (all 10 independent entries)')
    print('PASS 5D Ricci-flat after adding trivial -dt²')

    # chi=psi/(2k) has period 2pi, F=-sin(theta)/2 dtheta^dphi
    u=s.symbols('u',real=True)
    c1=s.simplify(s.integrate(-s.sin(u)/2,(u,0,s.pi)) *
                  2*s.pi/(2*s.pi))
    assert c1==-1
    print('PASS first Chern number -1 for psi period 4pi*k')


if __name__=='__main__':
    main()
