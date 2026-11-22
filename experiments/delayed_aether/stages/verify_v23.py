#!/usr/bin/env python3
"""V23: inhomogeneous spatial diffeo audit of ADM+memory, plus exact null-gravity benchmark.

This is a consistency test of an ADM-reduced *borrowed* Einstein-Hilbert action,
not a derivation of GR or emergent gravity from a medium.
Requires numpy, sympy, matplotlib. Deterministic; all outputs next to this file.
"""
from pathlib import Path
import csv, json, math
import numpy as np
import sympy as sp

ROOT=Path(__file__).resolve().parent


def exact_audit():
    J,c=sp.symbols('J c',positive=True)
    # Spatial density of a 3-volume with arbitrary exponent, when x->f(x), dx'=Jdx.
    weight=J**(1-c)
    linear_defect=sp.diff(weight,J).subs(J,1)
    assert sp.simplify(linear_defect-(1-c))==0
    assert sp.solve(sp.Eq(linear_defect,0),c)==[1]

    # An exact Rosen wave plus two identical, aligned null scalar profiles.
    u,k,Om,G,sigma=sp.symbols('u k Om G sigma', real=True)
    b=sp.log(sp.cos(Om*u))
    p=k*u
    P=sp.exp(b+p)
    Q=sp.exp(b-p)
    Ruu=sp.simplify(-sp.diff(P,u,2)/P-sp.diff(Q,u,2)/Q)
    assert sp.simplify(Ruu-2*(Om**2-k**2))==0
    # R_uu = 8 pi G * 2 sigma^2 for q=z=sigma u
    assert sp.simplify(Ruu.subs(Om**2, k**2+8*sp.pi*G*sigma**2)-16*sp.pi*G*sigma**2)==0

    # ADM split: ds²=-dt²+dx²+P(t-x)^2dy²+Q(t-x)^2dz².
    bd=sp.diff(b,u); bdd=sp.diff(b,u,2)
    R3=-4*bdd-6*bd**2-2*k**2
    K2minusKij2=2*(bd**2-k**2)
    H=sp.simplify(R3+K2minusKij2)
    assert sp.simplify(H-4*(Om**2-k**2))==0
    rho=2*sigma**2
    ham=sp.simplify(H-16*sp.pi*G*rho)
    assert sp.simplify(ham.subs(Om**2,k**2+8*sp.pi*G*sigma**2))==0
    # Convention: K_ij=+(dot gamma_ij)/(2N). Then D_j(K^j_x-d^j_x K)=G_tx=8piG T_tx.
    Dmom=2*(bdd+bd**2+k**2)
    Ttx=-2*sigma**2
    mom=sp.simplify(Dmom-8*sp.pi*G*Ttx)
    assert sp.simplify(mom.subs(Om**2,k**2+8*sp.pi*G*sigma**2))==0

    # Physical polarisations of transverse SPD matrix, with det=exp(4b)
    b0,p0,c0,eps=sp.symbols('b0 p0 c0 eps',real=True)
    hmat=sp.exp(2*b0)*sp.Matrix([[sp.exp(2*eps*p0),eps*c0],
                                 [eps*c0, sp.exp(-2*eps*p0)*(1+eps**2*c0**2)]])
    assert sp.simplify(hmat.det()-sp.exp(4*b0))==0
    lin=sp.simplify(hmat.diff(eps).subs(eps,0)/sp.exp(2*b0))
    assert lin==sp.Matrix([[2*p0,c0],[c0,-2*p0]])
    assert sp.trace(lin)==0
    return {'inhomogeneous_spatial_density_required_exponent':1,
            'gauge_anomalous_exponent_linear_defect':str(linear_defect),
            'null_wave_R_uu':str(Ruu), 'hamiltonian_constraint_symbolic':'0',
            'momentum_constraint_symbolic':'0', 'transverse_polarization_linearization':str(lin),
            'memory_in_exact_wave':'q=z=sigma*(t-x), so lag=0 and A=1'}


def fields_at(x,t):
    # Returns smooth, nontrivial analytic field jets, all periodic in x.
    def trig(A,m,omega,phase='sin'):
        arg=m*x+omega*t
        if phase=='sin':
            return (A*np.sin(arg), A*m*np.cos(arg), A*omega*np.cos(arg), -A*m*m*np.sin(arg))
        return (A*np.cos(arg), -A*m*np.sin(arg), -A*omega*np.sin(arg), -A*m*m*np.cos(arg))
    def total(*xs): return tuple(sum(tup[i] for tup in xs) for i in range(4))
    return {
        'a':total(trig(.045,1,.4),trig(.016,2,-.7,'cos')),
        'b':total(trig(.035,1,-.6,'cos'),trig(.014,3,.2)),
        'p':total(trig(.07,2,.3),trig(.02,1,-.6,'cos')),
        'c':total(trig(.05,1,.7,'cos'),trig(.015,3,-.4)),
        'N':total((1.25,0.,0.,0.),trig(.06,2,-.5,'cos')),
        'V':total(trig(.22,2,.6),trig(.05,1,-.2,'cos')),
        'q':total(trig(.38,2,-.7),trig(.11,1,.5,'cos')),
        'z':total(trig(-.22,3,.5,'cos'),trig(.08,2,-.9)),
    }


def h_jets(d):
    # H=e^(2b)[[e^(2p), c], [c, e^(-2p)(1+c^2)]]: SPD and det H=e^(4b).
    (b,bx,bt,bxx),(p,px,pt,pxx),(c,cx,ct,cxx)= (d[k] for k in ['b','p','c'])
    A=np.exp(2*b+2*p)
    Ax=A*2*(bx+px); At=A*2*(bt+pt)
    Axx=A*(2*(bxx+pxx)+4*(bx+px)**2)
    B=np.exp(2*b)*c
    Bx=np.exp(2*b)*(cx+2*bx*c)
    Bt=np.exp(2*b)*(ct+2*bt*c)
    Bxx=np.exp(2*b)*(cxx+4*bx*cx+(2*bxx+4*bx*bx)*c)
    F=np.exp(2*b-2*p)
    Fx=F*2*(bx-px); Ft=F*2*(bt-pt)
    Fxx=F*(2*(bxx-pxx)+4*(bx-px)**2)
    C=F*(1+c*c)
    Cx=Fx*(1+c*c)+F*(2*c*cx)
    Ct=Ft*(1+c*c)+F*(2*c*ct)
    Cxx=Fxx*(1+c*c)+4*Fx*c*cx +F*(2*cx*cx+2*c*cxx)
    H=np.array([[A,B],[B,C]])
    Hx=np.array([[Ax,Bx],[Bx,Cx]])
    Ht=np.array([[At,Bt],[Bt,Ct]])
    Hxx=np.array([[Axx,Bxx],[Bxx,Cxx]])
    return H,Hx,Ht,Hxx


def original_data(x,t):
    d=fields_at(x,t)
    H,Hx,Ht,Hxx=h_jets(d)
    return dict(a=d['a'][0],ax=d['a'][1],at=d['a'][2],
         N=d['N'][0],V=d['V'][0],Vx=d['V'][1],
         q=d['q'][0],qx=d['q'][1],qt=d['q'][2],
         z=d['z'][0],zx=d['z'][1],zt=d['z'][2],
         H=H,Hx=Hx,Ht=Ht,Hxx=Hxx)


def lag_density(v):
    a,ax,at,N,V,Vx=(v[k] for k in ['a','ax','at','N','V','Vx'])
    H,Hx,Ht,Hxx=(v[k] for k in ['H','Hx','Ht','Hxx'])
    hi=np.linalg.inv(H)
    U=hi@Hx
    trU=np.trace(U)
    trUx=np.trace(hi@Hxx-U@U)
    R3=np.exp(-2*a)*(-trUx+ax*trU-.25*trU**2-.25*np.trace(U@U))
    kx=(at-V*ax-Vx)/N
    Ktr=.5*hi@(Ht-V*Hx)/N
    kval=np.trace(Ktr)
    kin_grav=kx*kx+np.trace(Ktr@Ktr)-(kx+kval)**2
    vol=np.exp(a)*np.sqrt(np.linalg.det(H))
    Lg=vol*N*(R3+kin_grav)
    q,z,qt,qx,zt,zx=(v[k] for k in ['q','z','qt','qx','zt','zx'])
    A=1+2.5*np.tanh((q-z)/.45)**2
    ndq=(qt-V*qx)/N
    ndz=(zt-V*zx)/N
    pot=.5*1.3**2*(q-z)**2
    Lm=vol*N*(.5*(A*ndq**2+ndz**2)-.5*np.exp(-2*a)*(A*qx*qx+zx*zx)-pot)
    Lbad=vol*N*(.5*(A*(qt/N)**2+ndz**2)-.5*np.exp(-2*a)*(A*qx*qx+zx*zx)-pot)
    Lalt=Lg+.15*vol*N*R3**2 # spatially covariant alternative, NOT Einstein-Hilbert
    return np.array([Lg,Lm,Lbad,R3,kin_grav,vol,Lalt])


def transform_data(v,x,t,eps=.29,omega=.77):
    # Passive time-dependent x'=x+eps*sin(x)*sin(omega*t).
    J=1+eps*np.cos(x)*np.sin(omega*t)
    W=eps*omega*np.sin(x)*np.cos(omega*t)
    Jx=-eps*np.sin(x)*np.sin(omega*t)
    Jt=eps*omega*np.cos(x)*np.cos(omega*t)
    assert J>0.70
    o=dict(v)
    o['a']=v['a']-np.log(J)
    o['ax']=(v['ax']-Jx/J)/J
    o['at']=v['at']-W*v['ax']/J-Jt/J+W*Jx/J**2
    o['V']=J*v['V']-W
    o['Vx']=(Jx*v['V']+J*v['Vx']-Jt)/J
    o['Hx']=v['Hx']/J
    o['Hxx']=v['Hxx']/J**2-v['Hx']*(Jx/J**3)
    o['Ht']=v['Ht']-W*v['Hx']/J
    for sym in ['q','z']:
        o[sym+'x']=v[sym+'x']/J
        o[sym+'t']=v[sym+'t']-W*v[sym+'x']/J
    return o,J,W


def covariance_audit():
    rng=np.random.default_rng(20261123)
    errors=[]; bad_errors=[]; bad_shift=[]; curvature_errors=[]; geom_errors=[]; alt_errors=[]; alt_differences=[]
    records=[]
    for i in range(512):
        x,t=rng.uniform(0,2*np.pi),rng.uniform(-1.,2.)
        v=original_data(x,t)
        vt,J,W=transform_data(v,x,t)
        L=lag_density(v);Lprime=lag_density(vt)
        err=np.max(np.abs(J*Lprime[:2]-L[:2]))
        errors.append(err)
        bad_errors.append(abs(J*Lprime[2]-L[2]))
        curvature_errors.append(abs(Lprime[3]-L[3]))
        geom_errors.append(abs(J*Lprime[5]-L[5]))
        alt_errors.append(abs(J*Lprime[6]-L[6]))
        alt_differences.append(abs(L[6]-L[0]))
        # Incorrect: omit time-dependent -f_t part of shift.
        vw=dict(vt);vw['V']=J*v['V'];vw['Vx']=( (-.29*np.sin(x)*np.sin(.77*t))*v['V']+J*v['Vx'])/J
        lw=lag_density(vw)
        bad_shift.append(np.max(np.abs(J*lw[:2]-L[:2])))
        if i<20:
            records.append([i,x,t,J,W,L[0],J*Lprime[0],L[1],J*Lprime[1],L[2],J*Lprime[2],L[3],Lprime[3]])
    assert max(errors)<1e-11, max(errors)
    assert max(curvature_errors)<1e-11, max(curvature_errors)
    assert max(bad_errors)>1e-3, max(bad_errors)
    assert max(bad_shift)>1e-3,max(bad_shift)
    assert max(alt_errors)<1e-11,max(alt_errors)
    assert max(alt_differences)>1e-4,max(alt_differences)
    with (ROOT/'spatial_diffeomorphism_samples.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['id','x','t','Jacobian','f_t','L_gravity','J_L_gravity_prime','L_memory','J_L_memory_prime','L_bad','J_L_bad_prime','R3','R3_prime']);w.writerows(records)
    return {'samples':len(errors),'max_abs_correct_densities':float(max(errors)),
            'max_abs_curvature_scalar':float(max(curvature_errors)),
            'max_abs_volume_density':float(max(geom_errors)),
            'max_bad_advective_kinetic_defect':float(max(bad_errors)),
            'max_bad_shift_transformation_defect':float(max(bad_shift)),
            'max_abs_R3_squared_alternative_covariance_defect':float(max(alt_errors)),
            'max_difference_R3_squared_alternative_vs_EH':float(max(alt_differences))}, [errors,bad_errors,bad_shift,curvature_errors]


def exact_wave_audit():
    G=.03;k=.18;sigma=.07
    Omega=math.sqrt(k*k+8*math.pi*G*sigma*sigma)
    us=np.linspace(-3,3,601)
    bp=-Omega*np.tan(Omega*us)
    bpp=-Omega*Omega/(np.cos(Omega*us)**2)
    b=np.log(np.cos(Omega*us))
    p=k*us
    P=np.exp(b+p); Q=np.exp(b-p)
    R3=-4*bpp-6*bp*bp-2*k*k
    Kcomb=2*(bp*bp-k*k)
    Hsource=16*math.pi*G*2*sigma*sigma
    ham=R3+Kcomb-Hsource
    mom=2*(bpp+bp*bp+k*k) -8*math.pi*G*(-2*sigma*sigma)
    Ruu=2*(Omega**2-k**2)
    ricci_source=8*math.pi*G*2*sigma*sigma
    assert np.max(np.abs(ham))<1e-14
    assert np.max(np.abs(mom))<1e-14
    assert abs(Ruu-ricci_source)<1e-14
    # Count robustness: central focusing b''<0 and two independent null-wave amplitudes.
    with (ROOT/'exact_null_wave_constraints.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['u','P','Q','R3','K2minusKij2','hamiltonian_residual','momentum_residual','scalar_q','scalar_z']);
        for i,u in enumerate(us):w.writerow([u,P[i],Q[i],R3[i],Kcomb[i],ham[i],mom[i],sigma*u,sigma*u])
    return {'G':G,'polarization_k':k,'null_scalar_slope_sigma':sigma,'focus_frequency_Omega':Omega,
            'max_hamiltonian_constraint_residual':float(np.max(np.abs(ham))),
            'max_momentum_constraint_residual':float(np.max(np.abs(mom))),
            'max_null_einstein_residual':abs(Ruu-ricci_source),
            'R_uu':Ruu,'T_uu':2*sigma*sigma,
            'max_abs_transverse_plus_strain':float(np.max(np.abs(p))),
            'lag_and_hardening_active':False}, (us,P,Q,ham,mom,b,p)


def plots(cov,wave):
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    vals=[np.array(v) for v in cov]
    fig,ax=plt.subplots(figsize=(8.5,4.5))
    ax.plot(np.maximum(vals[0],1e-17),label='Correct ADM + memory (off shell)',lw=1.3)
    ax.plot(np.maximum(vals[1],1e-17),label='Wrong: ordinary time derivative for q',alpha=.8,lw=1)
    ax.plot(np.maximum(vals[2],1e-17),label='Wrong: omit shift in time-dependent relabeling',alpha=.75,lw=1)
    ax.set(yscale='log',xlabel='Random test state',ylabel='|Jacobian * transformed density - original|')
    ax.legend(fontsize=8); ax.grid(alpha=.25)
    fig.tight_layout();fig.savefig(ROOT/'nonlinear_spatial_gauge_test_v23.png',dpi=170);plt.close(fig)
    u,P,Q,ham,mom,b,p=wave
    fig,axs=plt.subplots(2,1,figsize=(8,7),sharex=True)
    axs[0].plot(u,P,label='Transverse length P(u)')
    axs[0].plot(u,Q,label='Transverse length Q(u)')
    axs[0].plot(u,np.exp(b),label='Shared focusing exp(b)',ls='--')
    axs[0].legend();axs[0].set_ylabel('Intrinsic transverse length')
    axs[1].plot(u,ham,label='Hamiltonian residual')
    axs[1].plot(u,mom,label='Momentum residual',alpha=.8)
    axs[1].set(xlabel='Null coordinate u=t-x',ylabel='Constraint residual')
    axs[1].legend();axs[1].grid(alpha=.25)
    fig.tight_layout();fig.savefig(ROOT/'exact_nonlinear_gravity_wave_v23.png',dpi=170);plt.close(fig)


def main():
    ex=exact_audit()
    cov,covdata=covariance_audit()
    wave,wavedata=exact_wave_audit()
    plots(covdata,wavedata)
    obj={'context':'V23: spatially inhomogeneous 3+1 ADM ansatz with two transverse polarizations and coupled scalar memory. GR gravitational action imposed.',
         'exact_symbolic_checks':ex,'random_diffeomorphism_audit':cov,'null_wave_and_matter_constraints':wave,
         'unresolved':['full unrestricted 3+1 spatial geometry','spin-2 emergence from primitive gel mechanics',
                       'finite nonzero memory lag in exact null-wave solution','irreversible covariant dissipation',
                       'continuous spectral stability of topological solitons','new observational predictions']}
    (ROOT/'audit_v23.json').write_text(json.dumps(obj,indent=2,ensure_ascii=False),encoding='utf-8')
    print(json.dumps(obj,indent=2,ensure_ascii=False))

if __name__=='__main__':main()