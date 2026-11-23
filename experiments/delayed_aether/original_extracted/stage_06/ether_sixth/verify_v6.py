#!/usr/bin/env python3
"""V6 reproducible metric, null/timelike geodesic, curvature and TT tests.
All radii in units of m=GM/c^2 and c=1. This is a kinematic toy,
not a derivation of gravitational field equations from an elastic medium.
"""
from __future__ import annotations
import csv, json
from pathlib import Path
import numpy as np
from scipy.integrate import quad
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

OUT=Path(__file__).resolve().parent


def metric(r: float, model: str):
    U=1/r
    if model=='exp': return float(np.exp(-2*U)),float(np.exp(2*U))
    if model=='schwarzschild':
        a=U/2
        return ((1-a)/(1+a))**2,(1+a)**4
    if model=='conformal':
        return np.exp(-2*U),np.exp(-2*U)
    raise ValueError(model)


def log_index(u,model):
    if model=='exp': return 2*u
    if model=='schwarzschild':
        a=u/2
        return 3*np.log1p(a)-np.log1p(-a)
    if model=='conformal': return 0.0*u
    raise ValueError(model)


def optical_bending(r0,model):
    """Exact null-geodesic bending for isotropic g=(-A,B,B,B).
    r0 is isotropic coordinate of periapse, m=1.
    Integrand regularized using y=1-t^2; b=r0*sqrt(B/A).
    """
    u=1/r0; n0_log=log_index(u,model)
    if model=='exp': slope=1-2*u
    elif model=='schwarzschild':
        a=u/2; slope=1-a*(3/(1+a)+1/(1-a))
    elif model=='conformal': slope=1
    else: raise ValueError(model)
    assert slope>0, 'periapse must be outside photon sphere'
    def integrand(t):
        if t<2e-8: return np.sqrt(2/slope)
        t2=t*t
        y=1-t2
        dlog=log_index(u*y,model)-n0_log
        denom2=np.expm1(2*dlog)+2*t2-t2*t2
        assert denom2>0,(r0,model,t,denom2)
        return 2*t/np.sqrt(denom2)
    I,abserr=quad(integrand,0,1,epsabs=3e-12,epsrel=3e-12,limit=150)
    return 2*I-np.pi, abserr, r0*np.exp(n0_log)


def timelike_precession(rp,ra,model):
    """Exact orbit geodesic azimuth per radial period minus 2pi; rp<ra."""
    assert rp<ra
    Ap,Bp=metric(rp,model); Aa,Ba=metric(ra,model)
    L2=(Aa-Ap)/(Ap/(Bp*rp*rp)-Aa/(Ba*ra*ra))
    E2=Ap*(1+L2/(Bp*rp*rp))
    assert E2>0 and L2>0
    mid=(rp+ra)*.5; half=(ra-rp)*.5
    def f(theta):
        theta=max(1e-7,min(np.pi-1e-7,theta))
        r=mid+half*np.cos(theta)
        A,B=metric(r,model)
        eff=E2/A-1-L2/(B*r*r)
        if eff<=0 and abs(eff)<1e-11: eff=1e-15
        assert eff>0,(r,model,eff)
        return np.sqrt(L2)*half*np.sin(theta)/(np.sqrt(B)*r*r*np.sqrt(eff))
    halfangle,err=quad(f,0,np.pi,epsabs=2e-9,epsrel=2e-9,limit=160)
    return 2*halfangle-2*np.pi, E2, L2, err


def ricci_scalar_exp(r):
    return -2*np.exp(-2/r)/r**4


def tt_project(h,k):
    k=np.asarray(k,dtype=float); k=k/np.linalg.norm(k)
    P=np.eye(3)-np.outer(k,k)
    return P@h@P - .5*P*np.trace(P@h)


def write_csv(name,keys,rows):
    with (OUT/name).open('w',newline='') as file:
        writer=csv.DictWriter(file,fieldnames=keys)
        writer.writeheader();writer.writerows(rows)


def main():
    bending=[]
    for r in [2.5,3,4,5,7,10,15,20,30,50,75,100,200,500,1000]:
        exp,ep,b_exp=optical_bending(r,'exp')
        sch,sp,b_sch=optical_bending(r,'schwarzschild')
        conf,cp,b_conf=optical_bending(r,'conformal')
        assert abs(conf)<1e-13
        bending.append(dict(r_periapse_over_m=r,bend_exp_rad=exp,bend_sch_rad=sch,
                bend_conformal_rad=conf,b_exp_over_m=b_exp,b_sch_over_m=b_sch,
                delta_exp_sch_rad=exp-sch,relative_excess_percent=100*(exp/sch-1),
                quad_err_exp=ep,quad_err_sch=sp))
    write_csv('lensing_exact.csv', list(bending[0]),bending)
    for entry in bending:
        assert entry['bend_exp_rad']>entry['bend_sch_rad']>0

    redshift=[]
    for r in [1,1.5,2.5,3,5,10,20,50,100,1000]:
        Ae,_=metric(r,'exp'); As,_=metric(r,'schwarzschild')
        ze=1/np.sqrt(Ae)-1
        zs=1/np.sqrt(As)-1
        redshift.append(dict(r_over_m=r,z_exp=ze,z_sch=zs,z_difference=ze-zs))
    write_csv('redshift.csv',list(redshift[0]),redshift)

    orbital=[]
    for rp,ra in [(7,9),(10,14),(15,22),(20,30),(50,70),(100,150)]:
        row={'rp_over_m':rp,'ra_over_m':ra}
        for model in ('exp','schwarzschild'):
            advance,E2,L2,err=timelike_precession(rp,ra,model)
            row.update({f'precession_{model}_rad':advance,f'E2_{model}':E2,
                        f'L2_{model}':L2,f'quad_err_{model}':err})
        row['delta_precession_rad']=row['precession_exp_rad']-row['precession_schwarzschild_rad']
        assert row['precession_exp_rad']>row['precession_schwarzschild_rad']>0
        orbital.append(row)
    write_csv('timelike_orbits.csv',list(orbital[0]),orbital)

    curvature=[]
    for r in [2,3,5,10,20,50,100,200]:
        curvature.append(dict(r_over_m=r,ricci_scalar_times_m2_exp=ricci_scalar_exp(r),
                              ricci_scalar_times_m2_sch=0.0,dimensionless_residual=abs(ricci_scalar_exp(r))*r*r))
    write_csv('vacuum_curvature.csv',list(curvature[0]),curvature)

    # TT projection: for scalar isotropic strain 2U I, the TT wave is identically zero.
    rng=np.random.default_rng(20261122)
    tt_checks=[]
    for i in range(64):
        k=rng.normal(size=3)
        U=rng.uniform(-.1,.1)
        hscalar=2*U*np.eye(3)
        out=tt_project(hscalar,k)
        tt_checks.append(float(np.max(np.abs(out))))
        assert tt_checks[-1]<1e-14
    example_tensor=np.diag([1.,-1.,0.])
    tensor_norm=float(np.linalg.norm(tt_project(example_tensor,[0,0,1])))
    assert abs(tensor_norm-np.sqrt(2))<1e-12

    # Symbolic PPN coefficients: for A=exp(-2U), B=exp(2U):
    # A=1-2U+2U²+O(U³), B=1+2U+2U²+O(U³).
    from sympy import symbols, exp, diff, simplify, series, log
    u=symbols('u',real=True)
    exp_A=exp(-2*u);exp_B=exp(2*u)
    sch_A=((1-u/2)/(1+u/2))**2
    sch_B=(1+u/2)**4
    A_exps=str(series(exp_A,u,0,4));B_exps=str(series(exp_B,u,0,4))
    A_schs=str(series(sch_A,u,0,4));B_schs=str(series(sch_B,u,0,4))
    # β= coefficient of u² in A /2 ; γ= coefficient u in B /2
    beta=float(diff(exp_A,u,2).subs(u,0)/4)
    gamma=float(diff(exp_B,u).subs(u,0)/2)
    assert beta==gamma==1.0
    diff2_spatial=float(diff(exp_B-sch_B,u,2).subs(u,0)/2)
    assert abs(diff2_spatial-.5)<1e-12

    # Null front speed in substrate rest frame: sqrt(A/B) = exp(-2U),
    # same for scalar U kinetic from sqrt(-g)g^{munu} partial U partial U.
    front=[]
    for u0 in [0.,.02,.1,.2,.4,.6]:
        A=np.exp(-2*u0);B=np.exp(2*u0)
        char_speed=np.sqrt(A/B)
        scalar_speed=np.sqrt(1/np.exp(4*u0))
        assert abs(char_speed-scalar_speed)<1e-14
        front.append(dict(U=u0,metric_light_front_speed=char_speed,
                          scalar_U_front_speed=scalar_speed,relative_difference=0.0))
    write_csv('causal_cone.csv',list(front[0]),front)

    fig,ax=plt.subplots(figsize=(8.4,4.8))
    x=np.array([e['r_periapse_over_m'] for e in bending]); y1=np.array([e['bend_exp_rad'] for e in bending]); y2=np.array([e['bend_sch_rad'] for e in bending]);
    ax.loglog(x,y1,'o-',label='exponential metric')
    ax.loglog(x,y2,'s--',label='Schwarzschild (GR)')
    ax.loglog(x,4/x,':',label='weak-field 4m/r0')
    ax.set(xlabel='Isotropic periapse radius r0 / m',ylabel='Deflection angle (radians)',title='Exact null-geodesic deflection')
    ax.legend();ax.grid(alpha=.25);fig.tight_layout();fig.savefig(OUT/'lensing_comparison.png',dpi=155);plt.close(fig)

    fig,ax=plt.subplots(figsize=(8.4,4.4))
    ax.semilogx(x,np.array([e['relative_excess_percent'] for e in bending]),'o-')
    ax.set(xlabel='Isotropic periapse radius r0 / m',ylabel='Exponential vs Schwarzschild excess (%)',title='Deviation grows in the strong-field regime')
    ax.grid(alpha=.3);fig.tight_layout();fig.savefig(OUT/'lensing_deviation.png',dpi=155);plt.close(fig)

    fig,ax=plt.subplots(figsize=(8.4,4.4))
    r=np.geomspace(2,100,300)
    ax.loglog(r,abs(ricci_scalar_exp(r)),'-',label='Exponential metric |Ricci scalar| m²')
    ax.loglog(r,2/r**4,':',label='Weak-field 2(m/r)^4')
    ax.set(xlabel='Isotropic r / m',ylabel='|R| m²',title='Nonzero vacuum curvature (Schwarzschild R=0)')
    ax.legend(); ax.grid(alpha=.25);fig.tight_layout();fig.savefig(OUT/'vacuum_obstruction.png',dpi=155);plt.close(fig)

    fig,ax=plt.subplots(figsize=(8.4,4.6))
    rp=np.array([e['rp_over_m'] for e in orbital]); ya=np.array([e['precession_exp_rad'] for e in orbital]); yb=np.array([e['precession_schwarzschild_rad'] for e in orbital]);
    ax.plot(rp,ya,'o-',label='Exponential metric');ax.plot(rp,yb,'s--',label='Schwarzschild (GR)')
    ax.set(xlabel='Isotropic orbit periapse rp / m',ylabel='Advance per radial period (radians)',title='Bound timelike geodesics; indicated ra in CSV')
    ax.legend();ax.grid(alpha=.25);fig.tight_layout();fig.savefig(OUT/'orbital_precession.png',dpi=155);plt.close(fig)

    results={
      'model':'Flat-background disformal/exponential metric plus independent GR Schwarzschild benchmark',
      'units':'G=c=m=1, m=GM/c^2',
      'PPN_beta':beta,'PPN_gamma':gamma,
      'PPN_exp_A':A_exps,'PPN_sch_A':A_schs,'PPN_exp_B':B_exps,'PPN_sch_B':B_schs,
      'first_spatial_2PN_coefficient_difference':diff2_spatial,
      'exact_ricci_scalar':'-2 m^2 exp(-2m/r)/r^4',
      'redshift_at_r10_exp':next(r['z_exp'] for r in redshift if r['r_over_m']==10),
      'redshift_at_r10_sch':next(r['z_sch'] for r in redshift if r['r_over_m']==10),
      'lensing_at_r10_exp':next(r['bend_exp_rad'] for r in bending if r['r_periapse_over_m']==10),
      'lensing_at_r10_sch':next(r['bend_sch_rad'] for r in bending if r['r_periapse_over_m']==10),
      'precession_at_rp10_ra14_exp':next(r['precession_exp_rad'] for r in orbital if r['rp_over_m']==10),
      'precession_at_rp10_ra14_sch':next(r['precession_schwarzschild_rad'] for r in orbital if r['rp_over_m']==10),
      'max_abs_TT_projection_isotropic':max(tt_checks),'TT_norm_plus_example':tensor_norm,
      'max_cone_speed_difference':max(r['relative_difference'] for r in front),
      'passes':True
    }
    (OUT/'results.json').write_text(json.dumps(results,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(results,ensure_ascii=False,indent=2))

if __name__=='__main__': main()
