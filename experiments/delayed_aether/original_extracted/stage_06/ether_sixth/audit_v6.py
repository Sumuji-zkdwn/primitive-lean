#!/usr/bin/env python3
"""Independent symbolic curvature and high precision geodesic checks.
Run after verify_v6.py and static_star_v6.py.
"""
from pathlib import Path
import json,csv
import sympy as s
import mpmath as mp
import numpy as np
OUT=Path(__file__).resolve().parent

def curvature_full(model):
    t,r,th,ph,m=s.symbols('t r theta phi m', positive=True)
    x=(t,r,th,ph)
    a=m/(2*r)
    if model=='exp':
        A=s.exp(-2*m/r);B=s.exp(2*m/r)
    elif model=='sch':
        A=((1-a)/(1+a))**2;B=(1+a)**4
    else:raise ValueError
    g=s.diag(-A,B,B*r**2,B*r**2*s.sin(th)**2)
    # Direct Christoffel and Ricci from the 4x4 metric (no 3+1 identities).
    inv=g.inv()
    gamma=[[[s.simplify(sum(inv[k,l]*(s.diff(g[l,j],x[i])+s.diff(g[l,i],x[j])-s.diff(g[i,j],x[l])) for l in range(4))/2)
            for j in range(4)] for i in range(4)] for k in range(4)]
    R=s.zeros(4,4)
    for i in range(4):
        for j in range(4):
            R[i,j]=s.simplify(sum(s.diff(gamma[k][i][j],x[k])-s.diff(gamma[k][i][k],x[j])+
                       sum(gamma[k][i][j]*gamma[l][k][l]-gamma[l][i][k]*gamma[k][j][l]
                           for l in range(4)) for k in range(4)))
    scalar=s.simplify(s.trace(inv*R))
    return s.simplify(R[0,0]),s.simplify(R[1,1]),s.simplify(R[2,2]),s.simplify(R[3,3]),scalar

def hp_index(U, model):
    if model=='exp':return mp.mpf(2)*U
    a=U/2
    return 3*mp.log1p(a)-mp.log1p(-a)

def lens_hp(r0,model):
    r0=mp.mpf(r0);u0=1/r0
    l0=hp_index(u0,model)
    if model=='exp': slope=1-2*u0
    else:
        a=u0/2; slope=1-a*(3/(1+a)+1/(1-a))
    def f(t):
        if t==0: return mp.sqrt(2/slope)
        t2=t*t
        delta=hp_index(u0*(1-t2),model)-l0
        dd=mp.expm1(2*delta)+2*t2-t2*t2
        if dd<=0 and t<mp.mpf('1e-16'):return mp.sqrt(2/slope)
        return 2*t/mp.sqrt(dd)
    return 2*mp.quad(f,[0,mp.mpf('.25'),mp.mpf('.75'),1])-mp.pi

def metric_hp(r,model):
    u=1/r
    if model=='exp':return mp.exp(-2*u),mp.exp(2*u)
    a=u/2
    return ((1-a)/(1+a))**2,(1+a)**4

def orbit_hp(rp,ra,model):
    rp,ra=mp.mpf(rp),mp.mpf(ra)
    Ap,Bp=metric_hp(rp,model);Aa,Ba=metric_hp(ra,model)
    L2=(Aa-Ap)/(Ap/(Bp*rp**2)-Aa/(Ba*ra**2))
    E2=Ap*(1+L2/(Bp*rp**2))
    half=(ra-rp)/2;mid=(rp+ra)/2
    def dlnA(r):
        if model=='exp':return 2/r**2
        a=1/(2*r)
        return 4*a/(r*(1-a*a))
    def dlnB(r):
        if model=='exp':return -2/r**2
        a=1/(2*r)
        return -4*a/(r*(1+a))
    def effprime(r):
        A,B=metric_hp(r,model)
        return -(E2/A)*dlnA(r) +L2/(B*r*r)*(dlnB(r)+2/r)
    def f(th):
        if th==0:
            return mp.sqrt(L2)*half/(mp.sqrt(Ba)*ra**2*mp.sqrt(-half*effprime(ra)/2))
        if th==mp.pi:
            return mp.sqrt(L2)*half/(mp.sqrt(Bp)*rp**2*mp.sqrt(half*effprime(rp)/2))
        r=mid+half*mp.cos(th)
        A,B=metric_hp(r,model)
        eff=E2/A-1-L2/(B*r*r)
        if eff<=0 and min(th,mp.pi-th)<mp.mpf('1e-17'):
            near=ra if th<mp.pi/2 else rp
            Bnear=Ba if th<mp.pi/2 else Bp
            return mp.sqrt(L2)*half/(mp.sqrt(Bnear)*near**2*mp.sqrt(abs(half*effprime(near))/2))
        return mp.sqrt(L2)*half*mp.sin(th)/(mp.sqrt(B)*r*r*mp.sqrt(eff))
    return 2*mp.quad(f,[0,mp.pi/2,mp.pi])-2*mp.pi

def main():
    expRic=curvature_full('exp')
    schRic=curvature_full('sch')
    t,r,th,ph,m=s.symbols('t r theta phi m', positive=True)
    expected=-2*m*m*s.exp(-2*m/r)/r**4
    assert s.simplify(expRic[-1]-expected)==0,expRic
    assert s.simplify(expRic[1]+2*m*m/r**4)==0,expRic
    assert all(s.simplify(val)==0 for i,val in enumerate(expRic[:-1]) if i!=1),expRic
    assert all(s.simplify(val)==0 for val in schRic),schRic
    print('Direct 4D Ricci tensor: exp nonvacuum / Schwarz zero confirmed')
    U,U_t,U_x,G=s.symbols('U U_t U_x G', real=True, positive=True)
    g00=-s.exp(-2*U);gii=s.exp(2*U)
    det_sqrt=s.exp(2*U)
    scalar_lagr=-det_sqrt*(s.exp(2*U)*(-U_t**2)+s.exp(-2*U)*(U_x**2))/(8*s.pi*G)
    expected_lagr=(s.exp(4*U)*U_t**2-U_x**2)/(8*s.pi*G)
    assert s.simplify(scalar_lagr-expected_lagr)==0
    assert s.simplify(s.diff(g00,U)+2*g00)==0
    assert s.simplify(s.diff(gii,U)-2*gii)==0
    print('Disformal kinetic prefactor and source variations confirmed')
    mp.mp.dps=43
    with (OUT/'lensing_exact.csv').open() as fh: lensrows=list(csv.DictReader(fh))
    with (OUT/'timelike_orbits.csv').open() as fh: orbitrows=list(csv.DictReader(fh))
    lens_results=[]
    for rad in (3,10,100):
        row=next(q for q in lensrows if float(q['r_periapse_over_m'])==rad)
        for model,field in [('exp','bend_exp_rad'),('sch','bend_sch_rad')]:
            hp=lens_hp(rad,model)
            err=abs(hp-mp.mpf(row[field]))
            assert err<mp.mpf('3e-10'),(rad,model,hp,row[field])
            lens_results.append(dict(r0=rad,model=model,hp=float(hp),delta=float(err)))
    orbit_results=[]
    for rp,ra in ((10,14),(20,30)):
        row=next(q for q in orbitrows if float(q['rp_over_m'])==rp and float(q['ra_over_m'])==ra)
        for model,col in [('exp','precession_exp_rad'),('sch','precession_schwarzschild_rad')]:
            hp=orbit_hp(rp,ra,model)
            err=abs(hp-mp.mpf(row[col]))
            assert err<mp.mpf('3e-8'),(rp,ra,model,hp,row[col])
            orbit_results.append(dict(rp=rp,ra=ra,model=model,hp=float(hp),delta=float(err)))
    print('High-precision quadrature confirmed:',max(r['delta'] for r in lens_results),max(r['delta'] for r in orbit_results))
    data={'pass':True,'symbolic_R_exp':str(expRic[-1]),
          'symbolic_Rrr_exp':str(expRic[1]),'symbolic_Ricci_sch_all_zero':True,
          'scalar_action_kinetic_check':True,
          'matter_metric_variation_check':True,
          'hp_lensing':lens_results,'hp_orbits':orbit_results}
    (OUT/'audit_v6.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(data,indent=2))

if __name__=='__main__':main()
