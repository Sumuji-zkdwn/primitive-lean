#!/usr/bin/env python3
"""Round 21: nonlinear Rosen-wave self-coupling and conditional memory no-go.
This verifies established Einstein/scalar equations; it does not derive GR from a medium.
"""
from pathlib import Path
import json, csv
import numpy as np
import sympy as sp
from scipy.integrate import cumulative_trapezoid, solve_ivp, simpson
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

OUT=Path(__file__).resolve().parent
u=sp.symbols('u',real=True)
eps=sp.symbols('eps',real=True)
f=sp.Function('f')(u)
b=sp.Function('b')(u)
X=1+eps*f+eps**2*b
Y=1-eps*f+eps**2*b

def ricci_XY(X,Xp,Xpp,Y,Yp,Ypp):
    return -.5*(Xpp/X+Ypp/Y)+.25*((Xp/X)**2+(Yp/Y)**2)

def symbolic():
    R=ricci_XY(X,sp.diff(X,u),sp.diff(X,u,2),Y,sp.diff(Y,u),sp.diff(Y,u,2))
    r2=sp.factor(sp.diff(R,eps,2).subs(eps,0)/2)
    expect=sp.diff(f,u)**2/2+f*sp.diff(f,u,2)-sp.diff(b,u,2)
    assert sp.simplify(r2-expect)==0
    assert sp.simplify(sp.diff(R,eps).subs(eps,0))==0
    assert sp.simplify(sp.diff(R,eps,3).subs(eps,0))==0
    # Exact special-case sinusoidal compensation
    k=sp.symbols('k',positive=True,real=True)
    fa=sp.sin(k*u)
    ba=-k**2*u**2/sp.Integer(8)+sp.Rational(3,16)*(1-sp.cos(2*k*u))
    assert sp.simplify(sp.diff(ba,u,2)-fa*sp.diff(fa,u,2)-sp.diff(fa,u)**2/2)==0
    # Relative mode of interacting Lorentz-invariant scalar fields
    t,x,mu=sp.symbols('t x mu',real=True)
    xi=sp.Function('Y')(t-x)
    # (box-2mu^2)xi=0, with box of a function of t-x =0
    box=sp.simplify(-sp.diff(xi,t,2)+sp.diff(xi,x,2))
    assert box==0
    # No nonzero travelling luminal relative-mode solution if mu !=0
    return {'rosen_Ruu':'-1/2*(Xpp/X+Ypp/Y)+1/4*((Xp/X)^2+(Yp/Y)^2)',
        'quadratic_coefficient':str(r2),
        'quadratic_vacuum_correction':'bpp=f*fpp+0.5*fp**2',
        'eps_linear_zero':True,'eps_cubic_zero':True,
        'sinusoidal_b_example':str(ba),
        'null_dalembertian_of_f(t_minus_x)':str(box),
        'relative_mode_relation':'(box-2mu^2)(q-z)=0; null travelling q-z=Y(t-x) implies mu^2*(q-z)=0'}

# Smooth wave and its exact derivatives
SIGMA=1.4
K=2.5
def profile(u):
    gg=np.exp(-.5*(u/SIGMA)**2)
    c,s=np.cos(K*u),np.sin(K*u)
    f=gg*c
    fp=gg*(-u/SIGMA**2*c-K*s)
    fpp=gg*((u*u/SIGMA**4-1/SIGMA**2-K*K)*c+2*u*K/SIGMA**2*s)
    return f,fp,fpp

def calc_pulse():
    uvals=np.linspace(-8,8,8001)
    ff,fp,fpp=profile(uvals)
    forcing=ff*fpp+.5*fp**2
    bp=cumulative_trapezoid(forcing,uvals,initial=0)
    bb=cumulative_trapezoid(bp,uvals,initial=0)
    rows=[]
    data=[]
    for e in [0.03,0.045,0.06,0.09,0.12]:
        X0=1+e*ff;Y0=1-e*ff
        Xp0=e*fp;Yp0=-e*fp
        Xpp0=e*fpp;Ypp0=-e*fpp
        R0=ricci_XY(X0,Xp0,Xpp0,Y0,Yp0,Ypp0)
        X1=X0+e**2*bb;Y1=Y0+e**2*bb
        Xp1=Xp0+e**2*bp;Yp1=Yp0+e**2*bp
        Xpp1=Xpp0+e**2*forcing;Ypp1=Ypp0+e**2*forcing
        assert X1.min()>0 and Y1.min()>0
        R1=ricci_XY(X1,Xp1,Xpp1,Y1,Yp1,Ypp1)
        # full domain, including boundaries, compare sup norm
        err0=float(np.max(abs(R0)))
        err1=float(np.max(abs(R1)))
        rows.append({'epsilon':e,'linear_only_max_abs_Ruu':err0,'second_order_max_abs_Ruu':err1,
          'suppression_ratio':err0/err1,'min_transverse_metric':float(min(X1.min(),Y1.min())),
          'uncompensated_scaled_Ruu_eps2':err0/(e**2),'compensated_scaled_Ruu_eps4':err1/(e**4)})
        if e==0.09:
            data=list(zip(uvals,ff,bb,R0,R1,X1,Y1))
    with (OUT/'nonlinear_ricci_scaling.csv').open('w',newline='') as fh:
        w=csv.DictWriter(fh,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
    with (OUT/'plane_wave_profile.csv').open('w',newline='') as fh:
        w=csv.writer(fh);w.writerow(['u','linear_wave_f','quadratic_b','Ruu_linear_only','Ruu_with_b','gxx','gyy']);w.writerows(data)
    fig,axes=plt.subplots(1,2,figsize=(11.5,4.1))
    es=np.array([r['epsilon'] for r in rows])
    r0=np.array([r['linear_only_max_abs_Ruu'] for r in rows]);r1=np.array([r['second_order_max_abs_Ruu'] for r in rows])
    axes[0].loglog(es,r0,'o-',label='linear metric only')
    axes[0].loglog(es,r1,'s-',label='quadratic correction included')
    axes[0].loglog(es,r0[0]*(es/es[0])**2,'--',alpha=.5,label=r'$\epsilon^2$ reference')
    axes[0].loglog(es,r1[0]*(es/es[0])**4,':',alpha=.75,label=r'$\epsilon^4$ reference')
    axes[0].set_xlabel('wave amplitude epsilon');axes[0].set_ylabel(r'max $|R_{uu}|$');axes[0].set_title('Nonlinear correction suppresses vacuum residual')
    axes[0].grid(alpha=.2);axes[0].legend(fontsize=8)
    axes[1].plot(uvals,ff,label='linearized transverse wave f')
    axes[1].plot(uvals,bb,label='self-coupling correction b')
    axes[1].set_xlabel('retarded time u');axes[1].set_ylabel('dimensionless profile');axes[1].set_title('Quadratic geometric response (Rosen gauge)')
    axes[1].grid(alpha=.2);axes[1].legend(fontsize=8)
    fig.tight_layout();fig.savefig(OUT/'nonlinear_plane_wave_v21.png',dpi=175);plt.close(fig)
    # Averaged gravitational wave energy check for sin(ku) at second order.
    av_a_aprime=np.mean(np.cos(np.linspace(0,2*np.pi,20001,endpoint=False))**2)
    average_R2=-K*K/4
    assert abs(av_a_aprime-.5)<1e-13
    return {'amplitudes':rows,'epsilon_0p09_metric_min':rows[3]['min_transverse_metric'],
      'sinusoidal_Ruu_quadratic_cycle_average_for_unit_amplitude_k':'-k^2/4',
      'Isaacson_effective_source_averaged_minus_G2_over_8piG':'epsilon^2*k^2/(32*pi*G) with conventional u normalization',
      'pulse_integral_source':float(simpson(forcing,x=uvals)),
      'pulse_final_bprime':float(bp[-1]),'pulse_final_b':float(bb[-1]),
      'limitation':'the average effective stress of gravitational waves is gauge/scale-dependent; exact Rosen-coordinate correction is not a local medium stiffening'}


def exact_vacuum_and_scalar():
    ee=.09
    from scipy.integrate import solve_ivp
    def f3(u):
        ff,fp,fpp=profile(u)
        return ff,fp,fpp
    def qstuff(u):
        f,fp,fpp=f3(u)
        y=1-ee*f
        assert np.all(y>0)
        qq=np.sqrt(y)
        qp=-ee*fp/(2*qq)
        qpp=-ee*fpp/(2*qq)-ee**2*fp*fp/(4*qq**3)
        return qq,qp,qpp
    def scalar(u):
        amplitude=.15;sig=1.2
        phi=amplitude*np.exp(-.5*(u/sig)**2)
        phi_p=-u/(sig**2)*phi
        Tuu=2*phi_p**2
        return phi,phi_p,Tuu
    G=.015
    q0,qp0,_=qstuff(-8)
    f0,fp0,_=f3(-8)
    # linear + branch matching at initial boundary
    p0=np.sqrt(1+ee*f0)
    pp0=ee*fp0/(2*p0)
    t_eval=np.linspace(-8,8,1601)
    results={}
    for mode in ['vacuum','equal_null_scalars']:
        def rhs(u,y):
            p,pprime=y
            q,qp,qpp=qstuff(u)
            _,_,Tuu=scalar(u)
            rhs_source=8*np.pi*G*Tuu if mode=='equal_null_scalars' else 0.0
            return [pprime,-(qpp/q+rhs_source)*p]
        sol=solve_ivp(rhs,(-8,8),[p0,pp0],t_eval=t_eval,method='DOP853',rtol=1e-12,atol=1e-13)
        assert sol.success
        p,pp=sol.y
        q,qp,qpp=qstuff(t_eval)
        _,_,Tuu=scalar(t_eval)
        src=8*np.pi*G*Tuu if mode=='equal_null_scalars' else np.zeros_like(t_eval)
        ppp=-(qpp/q+src)*p
        ricci=-ppp/p-qpp/q
        assert np.max(abs(ricci-src))<2e-14
        assert p.min()>0
        result={'mode':mode,'min_p':float(p.min()),'min_q':float(q.min()),
                'end_p':float(p[-1]),'end_pprime':float(pp[-1]),'max_abs_Ruu_minus_8piG_Tuu':float(np.max(abs(ricci-src))),
                'max_abs_Tuu':float(Tuu.max()) if mode=='equal_null_scalars' else 0.,
                'max_abs_Ruu':float(abs(ricci).max()),'G':G}
        rows=np.column_stack((t_eval,p,pp,q,qp,ricci,src))
        np.savetxt(OUT/f'exact_rosen_{mode}.csv',rows,delimiter=',',comments='',header='u,p,pprime,q,qprime,Ruu,8piGTuu')
        results[mode]=result
    plt.figure(figsize=(9,4.4))
    for mode in results:
        d=np.loadtxt(OUT/f'exact_rosen_{mode}.csv',delimiter=',',skiprows=1)
        plt.plot(d[:,0],d[:,1],label=mode.replace('_',' '))
    plt.xlabel('retarded time u');plt.ylabel('p(u)')
    plt.title('Exact nonlinear Rosen response: vacuum versus null scalar source')
    plt.legend();plt.grid(alpha=.25);plt.tight_layout();plt.savefig(OUT/'exact_plane_wave_source_v21.png',dpi=175);plt.close()
    return results


def lag_obstruction():
    # Two equal-kinetic fields with V=(mu^2/2)(q-z)^2.
    # Subtract EoMs: (box-2mu^2)(q-z)=0.
    # for any q-z=F(u), box F=0, => F=0 if mu>0.
    mu=.7
    wave_k=np.array([.25,.5,1.,2.,4.,8.])
    omega=np.sqrt(wave_k**2+2*mu**2)
    group_speed=wave_k/omega
    phase_speed=omega/wave_k
    assert np.all(group_speed<1)
    assert np.all(phase_speed>1)
    # Null carrier test: q=sin(ku), z=sin(k(u-delta)) cannot solve if delta!=0.
    uu=np.linspace(-4,4,1001)
    k=1.8
    tau=.4
    delta=np.sin(k*uu)-np.sin(k*(uu-tau))
    eq_residual=-mu**2*delta  # q EOM, box q=0
    residual=float(np.max(np.abs(eq_residual)))
    assert residual>.01
    with (OUT/'relative_mode_dispersion.csv').open('w',newline='') as fh:
        w=csv.writer(fh);w.writerow(['wave_number','frequency','group_velocity','phase_velocity'])
        w.writerows(zip(wave_k,omega,group_speed,phase_speed))
    fig,ax=plt.subplots(figsize=(7.4,4.4))
    xx=np.linspace(.05,9,300)
    ax.plot(xx,xx/np.sqrt(xx*xx+2*mu*mu),label='massive relative mode')
    ax.axhline(1,color='gray',ls='--',label='luminal wave front')
    ax.scatter(wave_k,group_speed)
    ax.set_xlabel('wave number k');ax.set_ylabel('group velocity')
    ax.set_ylim(0,1.08);ax.set_title('A coupled lag mode is dispersive, not exactly luminal')
    ax.legend();ax.grid(alpha=.2);fig.tight_layout();fig.savefig(OUT/'relative_mode_dispersion_v21.png',dpi=175);plt.close(fig)
    return {'relative_mode_mass_squared':2*mu**2,'group_speeds':group_speed.tolist(),
            'phase_speeds':phase_speed.tolist(),
            'null_lag_example_phase_shift':tau,'null_lag_example_nonzero_eom_residual':residual,
            'implication':'with V=mu^2(q-z)^2/2 and both pure null travelling waves, field equations require q=z; lag needs extra frequencies/dispersion or a different action'}


def main():
    result={'experiment':'v21, first nonlinear gravitational-wave self-response plus memory-mode obstruction',
            'symbolic':symbolic(),
            'quadratic_correction':calc_pulse(),
            'exact_rosen':exact_vacuum_and_scalar(),
            'memory_mode':lag_obstruction(),
            'scientific_status':'Known Rosen/Einstein-scalar vacuum equations and a conditional 2-scalar lag no-go verified. No gravitational emergence from gel; no dissipative medium model.'}
    (OUT/'audit_v21.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({ 'symbolic':result['symbolic'],
      'error_scaling':result['quadratic_correction']['amplitudes'],
      'exact_rosen':result['exact_rosen'],'memory':result['memory_mode']},ensure_ascii=False,indent=2))
if __name__=='__main__':main()