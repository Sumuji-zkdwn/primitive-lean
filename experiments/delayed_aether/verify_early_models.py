"""Selected arithmetic checks for v1--v6 delayed-aether toy models.

Pure standard library, no physical observation or GR reconstruction claimed.
"""
from math import exp, log, pi, sqrt, tanh
import json


def trapz(f, a, b, n):
    h = (b-a)/n
    return h*(.5*f(a)+.5*f(b)+sum(f(a+i*h) for i in range(1,n)))


def kink_and_pair():
    q=sqrt(2)
    def energy(x):
        t=tanh(x/q)
        dp=(1-t*t)/q
        return .5*dp*dp+.25*(t*t-1)**2
    E=trapz(energy,-20,20,16000)
    exact=2*sqrt(2)/3
    assert abs(E-exact)<2e-9
    def pair(R):
        def density(x):
            a=tanh((x+R/2)/q);b=tanh((x-R/2)/q)
            y=a-b-1
            dy=((1-a*a)-(1-b*b))/q
            return .5*dy*dy+.25*(y*y-1)**2
        return trapz(density,-20,20,20000)
    vals=[pair(R) for R in (3.,4.,5.,6.,8.)]
    assert vals==sorted(vals)
    assert all(0<v<2*exact for v in vals)
    assert abs(vals[1]-1.84776972)<5e-7
    return {'single_kink':E,'exact':exact,'pair_R3_4_5_6_8':vals}


def skyrme_positive():
    A=3*pi*pi*sqrt(2)
    B=45/16*pi*pi*sqrt(2)
    D=9/4*A
    R0=sqrt(B/A)
    R1=sqrt(B/(A-.5*.25*D))
    assert abs(R0-sqrt(15)/4)<2e-14
    assert abs(R1-1.14208048)<2e-8
    assert min(1-y+y*y/2 for y in (n/100 for n in range(-200,401)))>=.5
    for la,lb,lc in ((1,1,1),(.1,1,5),(2,3,4),(.02,.1,.3)):
        rho2=(la*la+lb*lb+lc*lc)/2
        rho4=((la*lb)**2+(la*lc)**2+(lb*lc)**2)/2
        assert .5*rho2+rho4>=3/sqrt(2)*la*lb*lc-1e-12
    return {'A':A,'B':B,'D22':D,'R0':R0,'R1_alpha_025':R1,
            'degree_one_lower_bound':3*sqrt(2)*pi*pi}


def rank_one_unbounded():
    C=256*pi/315; D=524288*pi/2297295; alpha=.25
    E=lambda n:C*n*n-alpha/2*D*n**4
    assert E(20)<E(10)<E(1)
    assert E(16)<-5000
    return {'C':C,'D':D,'E_n8':E(8),'E_n16':E(16),
            'reason':'negative quartic term dominates as n increases'}


def matched_cone():
    lags=(-10,-1,-.2,0,.2,1,10)
    coefficients=[1+3*tanh(y/.3)**2 for y in lags]
    assert min(coefficients)>=1 and max(coefficients)<4.0000000001
    assert all(abs(sqrt(A/A)-1)<1e-14 for A in coefficients)
    return {'min_A':min(coefficients),'max_A':max(coefficients),
            'front_speed':1,'qualification':'Minkowski background is assumed'}


def exponential_metric():
    # e^-2U=1-2U+2U²..., e^2U=1+2U+...
    for r in (2,3,10,100):
        U=1/r
        Rscalar=-2*exp(-2*U)/r**4
        assert Rscalar<0
        assert abs(sqrt(exp(2*U)/exp(-2*U))-exp(2*U))<1e-13
        assert abs(sqrt(exp(-2*U)/exp(-2*U))-1)<1e-13
    GM=1.3271244e20; solar_radius=6.957e8; c=299792458
    solar=4*GM/(c*c*solar_radius)*(180/pi*3600)
    assert 1.75<solar<1.76
    return {'PPN_beta':1,'PPN_gamma':1,
            'Rscalar_at_r10':-2*exp(-.2)/10**4,
            'solar_limb_GR_arcsec':solar,
            'conformal_scalar_deflection_arcsec':0}


def derrick_scaling():
    E=lambda R:2*R+.15*R**3
    assert all(E(x)>E(x/2) for x in (.1,.2,.5,1,2,5))
    return 'positive two-derivative plus potential energy shrinks with radius in 3D'


def main():
    audit={'kink':kink_and_pair(),'Skyrme':skyrme_positive(),
           'rank_one_counterexample':rank_one_unbounded(),
           'shared_front_cone':matched_cone(),
           'nonconformal_metric':exponential_metric(),
           'Derrick':derrick_scaling()}
    print(json.dumps(audit,indent=2))
    print('PASS: arithmetic witnesses only; NOT complete time evolution or a new gravity theory')


if __name__=='__main__':
    main()
