"""Exact analytic checks for one 8D Kähler internal metric candidate.

K = CP^2(Fubini-Study) x S^2(round) x S^2(axisymmetric).
The full geometric statements use standard theorems stated in the note:
this script checks the non-round sphere metric/curvature, Gauss--Bonnet,
and index/center arithmetic. It does not derive particles from 12D gravity.
"""
import sympy as s

def zero(expr):
    assert s.simplify(s.trigsimp(expr)) == 0, s.factor(expr)

def run():
    theta, u, ep = s.symbols('theta u epsilon', real=True)
    ep0=s.Rational(1,10)
    a=s.sin(theta)*(1+ep*s.sin(theta)**2)
    curvature=s.factor(-s.diff(a,theta,2)/a)
    K=(1-6*ep+9*ep*s.sin(theta)**2)/(1+ep*s.sin(theta)**2)
    zero(curvature-K)
    assert s.limit(a/theta,theta,0)==1
    assert s.diff(a,theta).subs(theta,0)==1
    assert s.diff(a,theta).subs(theta,s.pi)==-1
    assert s.series(a,theta,0,6).removeO().coeff(theta,2)==0
    assert s.series(a,theta,0,6).removeO().coeff(theta,4)==0
    zero(K.subs({ep:ep0,theta:0})-s.Rational(2,5))
    zero(K.subs({ep:ep0,theta:s.pi/2})-s.Rational(13,11))
    k_u=(1-6*ep+9*ep*u)/(1+ep*u)
    zero(s.diff(k_u,u)-2*ep*(4+3*ep)/(1+ep*u)**2)
    assert s.diff(k_u,u).subs({ep:ep0,u:s.Rational(1,2)})>0
    gauss_bonnet=s.simplify(-2*s.pi*s.integrate(s.diff(a,theta,2),(theta,0,s.pi)))
    zero(gauss_bonnet-4*s.pi)
    area=s.simplify(2*s.pi*s.integrate(a.subs(ep,ep0),(theta,0,s.pi)))
    assert area==64*s.pi/15

    # CP2 x CP1 x CP1 Spin-c index arithmetic, given HRR.
    p,q,r=s.symbols('p q r',integer=True)
    twice_index=(p+1)*(p+2)*(q+1)*(r+1)
    assert twice_index.subs({p:0,q:0,r:0})==2
    assert twice_index.subs({p:1,q:1,r:0})==12
    for k in range(-100,101):
        assert ((k+1)*(k+2))%2==0
    assert (twice_index/2).subs({p:1,q:1,r:0})==6

    # Necessary central-quotient condition; inserted SM hypercharges not derived.
    multiplets={
        'Q_left':(1,1,1),
        'up_right':(1,0,4),
        'down_right':(1,0,-2),
        'L_left':(0,1,-3),
        'electron_right':(0,0,-6),
        'sterile_neutrino':(0,0,0),
    }
    for name,(t,w,q6) in multiplets.items():
        assert (2*t+3*w+q6)%6==0,(name,t,w,q6)
    assert (2*1+3*1+0)%6!=0
    print('PASS: smooth poles, curvature, Gauss--Bonnet and area')
    print('K_pole=2/5, K_equator=13/11; area=',area)
    print('PASS: canonical Spin-c index arithmetic =1; twisted (1,1,0) index=6')
    print('PASS: six inserted SM representation charges satisfy Z6 center filter')
    print('DYNAMICAL COUNTEREXAMPLE: nonconstant K prevents this product from being Einstein')

if __name__=='__main__':
    run()
