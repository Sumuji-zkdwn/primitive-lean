#!/usr/bin/env python3
"""V28: two non-diagonal transverse metric polarizations + scalar-tensor canonical bracket.

This is a 1D-inhomogeneous symmetry reduction of 3+1 scalar-tensor ADM.
It does not derive the Einstein-Hilbert action, and the shape-wave simulation
fixes other degrees of freedom rather than solving all constraints.
"""
from pathlib import Path
import json,csv,hashlib
import numpy as np
import sympy as sp
import jax
jax.config.update('jax_enable_x64',True)
import jax.numpy as jnp
from jax import grad,jit
import scipy.integrate as si
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

DIR=Path(__file__).resolve().parent

def D(v,dx):
    return (jnp.roll(v,-1,axis=-1)-jnp.roll(v,1,axis=-1))/(2*dx)

def get_functions(f):
    a,s,b,w,chi,q=f
    F=2.+.35*jnp.tanh(chi)
    Fc=.35/(jnp.cosh(chi)**2)
    A=1.+1.8*jnp.tanh((q-chi)/.5)**2
    Dc=1.+1.5*Fc**2/F
    V=.5*(q-chi)**2+.07*chi**2
    return F,Fc,A,Dc,V

def H_jordan(f,p,N,dx,broken=False):
    a,s,b,w,chi,q=f
    Pa,Ps,Pb,Pw,pchi,pq=p
    F,Fc,A,Dc,V=get_functions(f)
    J=jnp.exp(a+2*s);W=jnp.exp(2*s-a)
    a_x,s_x,b_x,w_x,chi_x,q_x=D(f,dx)
    Fx=Fc*chi_x
    pi=Pa+Ps
    grav=(Pa**2-2*Pa*Ps+Pb**2)/(4*F*J)+jnp.exp(-4*b)*Pw**2/(F*J)
    mix=pchi-Fc*pi/(2*F) if not broken else pchi
    kinetics=grav+mix**2/(2*J*Dc)+pq**2/(2*J*A)
    spatial=W*(F*(-s_x**2+b_x**2+.25*jnp.exp(4*b)*w_x**2)
               -2*Fx*s_x+.5*(chi_x**2+A*q_x**2))+J*V
    boundary=-W*(2*F*s_x+Fx)
    return dx*jnp.sum(N*(kinetics+spatial)+D(N,dx)*boundary)

def H_einstein(f,p,N,dx):
    a,s,b,w,chi,q=f
    Pa,Ps,Pb,Pw,pchi,pq=p
    F,Fc,A,Dc,V=get_functions(f)
    shift=.5*jnp.log(F)
    ae=a+shift; se=s+shift
    JE=jnp.exp(ae+2*se);WE=jnp.exp(2*se-ae)
    chi_p=pchi-Fc*(Pa+Ps)/(2*F)
    N_e=jnp.sqrt(F)*N
    Gchi=Dc/F;Gq=A/F
    kin=(Pa**2-2*Pa*Ps+Pb**2)/(4*JE)+jnp.exp(-4*b)*Pw**2/JE
    kin+=chi_p**2/(2*JE*Gchi)+pq**2/(2*JE*Gq)
    _,se_x,b_x,w_x,chi_x,q_x=D(jnp.stack([ae,se,b,w,chi,q]),dx)
    space=WE*(-se_x**2+b_x**2+.25*jnp.exp(4*b)*w_x**2+
              .5*(Gchi*chi_x**2+Gq*q_x**2))+JE*V/F**2
    return dx*jnp.sum(N_e*(kin+space)-D(N_e,dx)*WE*(2*se_x))

def make_state(n,variant='standard'):
    x=jnp.arange(n)*(2*jnp.pi/n)
    a=.14*jnp.sin(x+.12)+.045*jnp.cos(2*x)
    s=-.08*jnp.cos(x+.43)+.06*jnp.sin(3*x)
    b=.075*jnp.sin(2*x+.5)+.035*jnp.cos(3*x+.3)
    w=.22*jnp.cos(x-.15)+.12*jnp.sin(3*x+.6)
    chi=.27*jnp.sin(x-.2)+.17*jnp.cos(2*x+.1)
    q=.20*jnp.cos(x+.4)+.28*jnp.sin(3*x-.1)
    Pa=.22+.16*jnp.sin(x+.35)+.08*jnp.cos(3*x-.3)
    Ps=-.10+.17*jnp.cos(2*x+.2)+.13*jnp.sin(x-.5)
    Pb=.12*jnp.sin(3*x-.1)+.06*jnp.cos(2*x+.2)
    Pw=.18*jnp.cos(2*x+.4)+.07*jnp.sin(4*x-.2)
    pchi=.26+.25*jnp.sin(2*x-.7)+.16*jnp.cos(x-.1)
    pq=-.15+.23*jnp.cos(3*x+.4)+.12*jnp.sin(x+.5)
    N=1+.31*jnp.cos(x+.25)+.13*jnp.sin(2*x+.7)+.07*jnp.cos(4*x)
    M=.90+.27*jnp.sin(x+.12)+.11*jnp.cos(3*x-.2)+.09*jnp.sin(4*x+.3)
    f=jnp.stack([a,s,b,w,chi,q]);p=jnp.stack([Pa,Ps,Pb,Pw,pchi,pq])
    if variant=='reverse_shear':
        f=f.at[3].set(-1.5*f[3]+.04*jnp.cos(5*x))
        p=p.at[3].set(-.7*p[3]+.07*jnp.sin(2*x))
    elif variant=='strong_memory':
        f=f.at[4].set(1.4*f[4]-.07*jnp.sin(4*x))
        f=f.at[5].set(-.9*f[5]+.09*jnp.cos(5*x))
    elif variant=='nonzero_cross':
        f=f.at[3].set(.65*f[3]+.17*jnp.sin(5*x))
        p=p.at[2].set(p[2]+.25*jnp.sin(4*x))
    return f,p,N,M,2*np.pi/n

def bracket(f,p,N,M,dx,broken=False):
    dfN,dpN=grad(lambda g,pi:H_jordan(g,pi,N,dx,broken),argnums=(0,1))(f,p)
    dfM,dpM=grad(lambda g,pi:H_jordan(g,pi,M,dx,broken),argnums=(0,1))(f,p)
    return jnp.sum(dfN*dpM-dpN*dfM)/dx

def diffeo(f,p,N,M,dx):
    a=f[0]
    u=jnp.exp(-2*a)*(N*D(M,dx)-M*D(N,dx))
    density=jnp.sum(p*D(f,dx),axis=0)-D(p[0],dx)
    return dx*jnp.sum(u*density)

@jit
def triple(f,p,N,M,dx):
    return jnp.array([bracket(f,p,N,M,dx,False),bracket(f,p,N,M,dx,True),diffeo(f,p,N,M,dx), H_jordan(f,p,N,dx),H_einstein(f,p,N,dx)])

def symbolic():
    F,Fx,sx,bx,wx,chix,qx,Dchi,A,N,Nx,W,eb=sp.symbols('F Fx sx bx wx chix qx Dchi A N Nx W eb',real=True)
    r=Fx/(2*F)
    j=N*W*(F*(-sx*sx+bx*bx+eb*wx*wx/4)-2*Fx*sx+(chix**2+A*qx**2)/2)-Nx*W*(2*F*sx+Fx)
    e=N*W*F*(-(sx+r)**2+bx*bx+eb*wx*wx/4+(Dchi/F*chix**2+A/F*qx**2)/2)-(Nx*F*W+N*W*Fx/2)*2*(sx+r)
    # Substitute Dchi=1+3Fc²/(2F) and Fx=Fc chi_x.
    expr=sp.factor((e-j).subs(Dchi,1+3*Fx**2/(2*F*chix**2)))
    assert expr==0,expr
    Pa,Ps,Pb,Pw,pchi,fc,da,ds,db,dw,dch=sp.symbols('Pa Ps Pb Pw pchi fc da ds db dw dch')
    orig=Pa*da+Ps*ds+Pb*db+Pw*dw+pchi*dch
    transformed=Pa*(da+fc*dch/(2*F))+Ps*(ds+fc*dch/(2*F))+Pb*db+Pw*dw+(pchi-fc*(Pa+Ps)/(2*F))*dch
    assert sp.simplify(orig-transformed)==0
    # Direct transverse metric trace confirms nonlinear cross mode coefficient.
    b,s,w,bd,sd,wd=sp.symbols('b s w bd sd wd', real=True)
    MM=sp.Matrix([[sp.exp(2*b),sp.exp(2*b)*w],[sp.exp(2*b)*w,sp.exp(-2*b)+sp.exp(2*b)*w*w]])
    hh=sp.exp(2*s)*MM
    hd=hh.diff(s)*sd+hh.diff(b)*bd+hh.diff(w)*wd
    sh=sp.simplify(hh.inv()*hd/2)
    sq=sp.simplify(sp.trace(sh*sh))
    assert sp.simplify(sq-(2*sd**2+2*bd**2+sp.exp(4*b)*wd**2/2))==0
    assert sp.simplify(hh.det()-sp.exp(4*s))==0
    return dict(jordan_einstein_spatial='exact_zero',canonical_one_form='exact_zero',shape_trace_square=str(sq),transverse_metric_determinant='exp(4*s)')

# Independently check spatial scalar curvature from Christoffel symbols. Grid-point
# derivatives use spectral (Fourier) derivatives, unrelated to the central scheme above.
def deriv_fft(v,order=1):
    n=len(v); kk=np.fft.fftfreq(n,d=2*np.pi/n)*2*np.pi
    return np.fft.ifft((1j*kk)**order*np.fft.fft(v)).real

def ricci_direct(n=128):
    x=np.linspace(0,2*np.pi,n,endpoint=False)
    a=.13*np.sin(x+.2);s=.08*np.sin(2*x-.4);b=.065*np.cos(3*x+.1);w=.16*np.sin(x+.3)
    ga=np.zeros((n,3,3))
    ga[:,0,0]=np.exp(2*a)
    ga[:,1,1]=np.exp(2*s+2*b)
    ga[:,1,2]=ga[:,2,1]=np.exp(2*s+2*b)*w
    ga[:,2,2]=np.exp(2*s)*(np.exp(-2*b)+np.exp(2*b)*w*w)
    inv=np.linalg.inv(ga)
    gx=np.stack([np.stack([deriv_fft(ga[:,i,j]) for j in range(3)],axis=-1) for i in range(3)],axis=1)
    Gamma=np.zeros((n,3,3,3))
    for i in range(3):
        for j in range(3):
            for k in range(3):
                # Gamma^k_ij=0.5 g^{kl}(d_i g_jl+d_j g_il-d_l g_ij), only d_0 ≠0.
                for l in range(3):
                    Gamma[:,k,i,j]+=.5*inv[:,k,l]*((i==0)*gx[:,j,l]+(j==0)*gx[:,i,l]-(l==0)*gx[:,i,j])
    Gamma_x=np.stack([np.stack([np.stack([deriv_fft(Gamma[:,k,i,j]) for j in range(3)],axis=-1) for i in range(3)],axis=1) for k in range(3)],axis=1)
    R=np.zeros((n,3,3))
    for i in range(3):
        for j in range(3):
            # R_ij = d_k Gamma^k_ij - d_j Gamma^k_ik + Gamma^k_ij Gamma^l_kl - Gamma^k_il Gamma^l_jk.
            R[:,i,j]+=Gamma_x[:,0,i,j]
            if j==0:
                for k in range(3): R[:,i,j]-=Gamma_x[:,k,i,k]
            for k in range(3):
                for l in range(3):
                    R[:,i,j]+=Gamma[:,k,i,j]*Gamma[:,l,k,l]-Gamma[:,k,i,l]*Gamma[:,l,j,k]
    scalar=np.einsum('nij,nij->n',inv,R)
    ax=deriv_fft(a);sx=deriv_fft(s);sxx=deriv_fft(s,2);bx=deriv_fft(b);wx=deriv_fft(w)
    closed=-np.exp(-2*a)*(4*sxx-4*ax*sx+6*sx*sx+2*bx*bx+.5*np.exp(4*b)*wx*wx)
    return float(np.max(np.abs(scalar-closed))),float(np.max(abs(scalar))),float(np.max(abs(closed)))

# NumPy finite-difference bracket: independent from JAX derivatives/implementation.
def Dnp(v,dx):return (np.roll(v,-1,axis=-1)-np.roll(v,1,axis=-1))/(2*dx)
def H_numpy(f,p,N,dx,broken=False):
    a,s,b,w,chi,q=f; Pa,Ps,Pb,Pw,pchi,pq=p
    F=2+.35*np.tanh(chi);Fc=.35/np.cosh(chi)**2
    A=1+1.8*np.tanh((q-chi)/.5)**2;Dc=1+1.5*Fc**2/F
    V=.5*(q-chi)**2+.07*chi**2
    J=np.exp(a+2*s);W=np.exp(2*s-a)
    _,sx,bx,wx,chix,qx=Dnp(f,dx)
    mix=pchi-Fc*(Pa+Ps)/(2*F) if not broken else pchi
    kin=(Pa**2-2*Pa*Ps+Pb**2)/(4*F*J)+np.exp(-4*b)*Pw**2/(F*J)+mix**2/(2*J*Dc)+pq**2/(2*J*A)
    Fx=Fc*chix
    spa=W*(F*(-sx**2+bx**2+np.exp(4*b)*wx**2/4)-2*Fx*sx+(chix**2+A*qx**2)/2)+J*V
    return dx*np.sum(N*(kin+spa)-Dnp(N,dx)*W*(2*F*sx+Fx))

def independent_bracket(n=8):
    f,p,N,M,dx=make_state(n)
    ff=np.array(f);pp=np.array(p);nn=np.array(N);mm=np.array(M)
    def gH(smear):
        eps=2e-6
        df=np.zeros_like(ff);dp=np.zeros_like(pp)
        for k in range(6):
            for j in range(n):
                f1=ff.copy();f2=ff.copy();f1[k,j]+=eps;f2[k,j]-=eps
                df[k,j]=(H_numpy(f1,pp,smear,dx)-H_numpy(f2,pp,smear,dx))/(2*eps)
                p1=pp.copy();p2=pp.copy();p1[k,j]+=eps;p2[k,j]-=eps
                dp[k,j]=(H_numpy(ff,p1,smear,dx)-H_numpy(ff,p2,smear,dx))/(2*eps)
        return df,dp
    dfN,dpN=gH(nn);dfM,dpM=gH(mm)
    npbr=float(np.sum(dfN*dpM-dpN*dfM)/dx)
    jbr=float(bracket(f,p,N,M,dx))
    return {'n':n,'numpy_finite_difference_bracket':npbr,'jax_autodiff_bracket':jbr,'absolute_difference':abs(npbr-jbr)}

def shapes_frozen_memory():
    # Consistent Hamiltonian evolution in the TWO-polarization SHAPE sector only:
    # H=integral [pb²/(4F)+exp(-4b)pw²/F +F*(b_x²+exp(4b)w_x²/4)].
    # a=s=0 and chi(x) are frozen externally, so NOT a fully constrained GR solution.
    n=256; dx=2*np.pi/n; x=np.arange(n)*dx
    chi=.4*np.cos(x-.6)+.18*np.sin(2*x)
    F=2+.35*np.tanh(chi)
    d=lambda u:(np.roll(u,-1)-np.roll(u,1))/(2*dx)
    def energy(Y):
        b,w,pb,pw=np.split(Y,4)
        return dx*np.sum(pb**2/(4*F)+np.exp(-4*b)*pw**2/F+F*(d(b)**2+np.exp(4*b)*d(w)**2/4))
    def rhs(t,Y):
        b,w,pb,pw=np.split(Y,4)
        ex=np.exp(4*b)
        bdot=pb/(2*F);wdot=2*pw/(F*ex)
        pbdot=2*d(F*d(b))+4*pw**2/(F*ex)-F*ex*d(w)**2
        pwdot=.5*d(F*ex*d(w))
        return np.concatenate([bdot,wdot,pbdot,pwdot])
    dist=np.angle(np.exp(1j*(x-2.3)))
    w=.25*np.exp(-(dist/.46)**2)
    b=np.zeros(n);pb=np.zeros(n)
    pw=-.5*F*d(w) # right-moving initial approximate characteristic wave
    Y0=np.concatenate([b,w,pb,pw]);E0=energy(Y0)
    tt=np.linspace(0,3.2,65)
    sol=si.solve_ivp(rhs,(tt[0],tt[-1]),Y0,method='DOP853',rtol=2e-11,atol=2e-12,t_eval=tt,max_step=dx*.4)
    assert sol.success,sol.message
    rows=[]
    for i,t in enumerate(tt):
        B,W,PB,PW=np.split(sol.y[:,i],4)
        E=energy(sol.y[:,i])
        rows.append(dict(time=float(t),max_b=float(np.max(abs(B))),max_w=float(np.max(abs(W))),energy=float(E),relative_energy_error=float((E-E0)/E0)))
    assert max(abs(r['relative_energy_error']) for r in rows)<1e-7
    # Nonzero plus generated from initially pure cross data: nonlinear polarization mixing.
    assert rows[15]['max_b']>0.0001
    with open(DIR/'nonlinear_polarization_history_v28.csv','w',newline='') as out:
        wr=csv.DictWriter(out,list(rows[0]));wr.writeheader();wr.writerows(rows)
    fig,ax=plt.subplots(figsize=(8,4.5));ax.plot(tt,[r['max_w'] for r in rows],label='cross w');ax.plot(tt,[r['max_b'] for r in rows],label='plus b (induced)');ax.set(xlabel='Model time',ylabel='Maximum amplitude',title='Two-polarization nonlinear shape sector (fixed memory profile)');ax.grid(alpha=.2);ax.legend();fig.tight_layout();fig.savefig(DIR/'nonlinear_polarization_exchange_v28.png',dpi=160);plt.close(fig)
    fig,ax=plt.subplots(figsize=(8,4.5));ax.plot(tt,[r['relative_energy_error'] for r in rows]);ax.set(xlabel='Model time',ylabel='(E(t)-E(0))/E(0)',title='Conservation of the frozen-background shape Hamiltonian');ax.grid(alpha=.2);fig.tight_layout();fig.savefig(DIR/'shape_energy_audit_v28.png',dpi=160);plt.close(fig)
    return {'grid_points':n,'initial_energy':E0,'max_plus_generated':max(r['max_b'] for r in rows),'max_relative_energy_error':max(abs(r['relative_energy_error']) for r in rows),'final_plus':rows[-1]['max_b'],'note':'Fixed chi and a=s=0; not full Einstein constraints or tensor linearization on curved solutions.'}

def main():
    print('Symbolic checks',flush=True); proof=symbolic()
    print('Independent metric curvature',flush=True); curv=ricci_direct()
    print('curvature',curv,flush=True); assert curv[0]<1e-8
    rows=[]
    for mode in ['standard','reverse_shear','strong_memory','nonzero_cross']:
        for n in [32,64,128,256]:
            f,p,N,M,dx=make_state(n,mode)
            br,bad,target,hj,he=map(float,triple(f,p,N,M,dx))
            rows.append(dict(mode=mode,n=n,dx=dx,bracket=br,target=target,correct_error=br-target,broken_error=bad-target,frame_error=he-hj))
            print(mode,n,'bracket error',br-target,'omit mixing',bad-target,'frame',he-hj,flush=True)
    for mode in ['standard','reverse_shear','strong_memory','nonzero_cross']:
        rs=[r for r in rows if r['mode']==mode]
        assert abs(rs[-1]['correct_error'])<abs(rs[-2]['correct_error'])/3.5
        assert abs(rs[-1]['broken_error'])>10*abs(rs[-1]['correct_error'])
        assert abs(rs[-1]['frame_error'])<abs(rs[-2]['frame_error'])/3.4
    with open(DIR/'offdiagonal_bracket_convergence_v28.csv','w',newline='') as out:
        wr=csv.DictWriter(out,list(rows[0]));wr.writeheader();wr.writerows(rows)
    independent=independent_bracket(8)
    print('independent bracket',independent,flush=True)
    assert independent['absolute_difference']<1e-8
    fig,ax=plt.subplots(figsize=(8,4.6))
    standard=[r for r in rows if r['mode']=='standard']
    ax.loglog([r['dx'] for r in standard],[abs(r['correct_error']) for r in standard],'o-',label='Correct coupling')
    ax.loglog([r['dx'] for r in standard],[abs(r['broken_error']) for r in standard],'s-',label='Omit canonical momentum mixing')
    ax.loglog([r['dx'] for r in standard],[abs(standard[-1]['correct_error'])*(r['dx']/standard[-1]['dx'])**2 for r in standard],'--',c='gray',label='Second-order slope')
    ax.set(xlabel='Grid spacing',ylabel='Absolute bracket residual',title='Non-diagonal metric + memory: H-H constraint bracket')
    ax.legend();ax.grid(alpha=.2,which='both');fig.tight_layout();fig.savefig(DIR/'offdiagonal_constraint_closure_v28.png',dpi=160);plt.close(fig)
    fig,ax=plt.subplots(figsize=(8,4.6))
    ax.loglog([r['dx'] for r in standard],[abs(r['frame_error']) for r in standard],'o-',label='Jordan vs Einstein')
    ax.loglog([r['dx'] for r in standard],[abs(standard[-1]['frame_error'])*(r['dx']/standard[-1]['dx'])**2 for r in standard],'--',c='gray',label='Second-order slope')
    ax.set(xlabel='Grid spacing',ylabel='Hamiltonian difference',title='Conformal frame identity with both polarizations')
    ax.legend();ax.grid(alpha=.2,which='both');fig.tight_layout();fig.savefig(DIR/'frame_equivalence_v28.png',dpi=160);plt.close(fig)
    print('Nonlinear shape subsystem',flush=True); shape=shapes_frozen_memory()
    print('shape:',shape,flush=True)
    audit={'symbolic':proof,'curvature_audit':{'max_difference':curv[0],'max_R_christoffel':curv[1],'max_R_closed':curv[2]},'off_shell_brackets':rows,'independent_numpy':independent,'shape_wave':shape,'limits':['Not full 3D arbitrary metric','Not derivation of Einstein-Hilbert action','Memory field is reversible','Shape-wave simulation is restricted and on fixed background','Discrete brackets close only asymptotically']}
    (DIR/'audit_v28.json').write_text(json.dumps(audit,indent=2,ensure_ascii=False)+'\n')
    print('V28 ALL TESTS PASSED',flush=True)
if __name__=='__main__':main()
