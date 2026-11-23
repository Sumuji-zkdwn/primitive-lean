#!/usr/bin/env python3
"""Additional v28: explicit *lag-controlled* bounded tensor stiffness F(q-chi).

Two scalar momenta MUST both mix with the metric-trace momentum. No inference of
microscopic spacetime emergence is claimed: this is a pre-specified scalar-tensor action.
"""
from pathlib import Path
import json,csv
import numpy as np
import sympy as sp
import jax
jax.config.update('jax_enable_x64',True)
import jax.numpy as jnp
from jax import grad,jit
from verify_v28 import make_state,D,diffeo
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
BASE=Path(__file__).resolve().parent

def functions(f):
    chi,q=f[4],f[5]
    y=q-chi
    t=jnp.tanh(y/.45)
    F=2.+1.2*t*t
    Fy=2*1.2/.45*t*(1-t*t)
    Fchi=-Fy;Fq=Fy
    A=1.+1.8*jnp.tanh(y/.5)**2
    V=.5*y*y+.07*chi*chi
    return F,Fchi,Fq,A,V

def invquad(schi,sq,Fchi,Fq,F,A):
    k=1.5/F
    z=Fchi**2+Fq**2/A
    dot=Fchi*schi+Fq*sq/A
    return schi**2+sq**2/A-(k/(1+k*z))*dot**2

def HJ(f,p,N,dx,kind='full'):
    a,s,b,w,chi,q=f
    Pa,Ps,Pb,Pw,pchi,pq=p
    F,Fchi,Fq,A,V=functions(f)
    J=jnp.exp(a+2*s);W=jnp.exp(2*s-a)
    _,sx,bx,wx,chix,qx=D(f,dx)
    Fx=Fchi*chix+Fq*qx
    tracepi=(Pa+Ps)/2
    scalarpchi=pchi-Fchi/F*tracepi if kind=='full' else pchi
    scalarpq=pq-Fq/F*tracepi if kind=='full' else pq
    hkin=(Pa**2-2*Pa*Ps+Pb**2)/(4*F*J)+jnp.exp(-4*b)*Pw**2/(F*J)
    skin=invquad(scalarpchi,scalarpq,Fchi,Fq,F,A)/(2*J)
    spatial=W*(F*(-sx*sx+bx*bx+jnp.exp(4*b)*wx*wx/4)
               -2*Fx*sx+(chix*chix+A*qx*qx)/2)+J*V
    return dx*jnp.sum(N*(hkin+skin+spatial)-D(N,dx)*W*(2*F*sx+Fx))

def HE(f,p,N,dx):
    a,s,b,w,chi,q=f
    Pa,Ps,Pb,Pw,pchi,pq=p
    F,Fchi,Fq,A,V=functions(f)
    shift=.5*jnp.log(F); aE=a+shift;sE=s+shift
    JE=jnp.exp(aE+2*sE);WE=jnp.exp(2*sE-aE)
    NEW=jnp.sqrt(F)*N
    pi=(Pa+Ps)/2
    schi=pchi-Fchi/F*pi;sq=pq-Fq/F*pi
    hkin=(Pa**2-2*Pa*Ps+Pb**2)/(4*JE)+jnp.exp(-4*b)*Pw**2/JE
    # In E frame inverse scalar metric = F D^-1
    skin=F*invquad(schi,sq,Fchi,Fq,F,A)/(2*JE)
    _,sEx,bx,wx,chix,qx=D(jnp.stack([aE,sE,b,w,chi,q]),dx)
    Fx=Fchi*chix+Fq*qx
    # D_ij/F grad phi grad phi = (chi_x²+A q_x²)/F +3Fx²/(2F²)
    scalar_gradient=(chix**2+A*qx**2)/F+1.5*Fx**2/F**2
    sp=WE*(-sEx*sEx+bx*bx+jnp.exp(4*b)*wx*wx/4+scalar_gradient/2)+JE*V/F**2
    return dx*jnp.sum(NEW*(hkin+skin+sp)-D(NEW,dx)*WE*(2*sEx))

def PB(f,p,N,M,dx,kind='full'):
    (dfn,dpn)=grad(lambda ff,pp:HJ(ff,pp,N,dx,kind),argnums=(0,1))(f,p)
    (dfm,dpm)=grad(lambda ff,pp:HJ(ff,pp,M,dx,kind),argnums=(0,1))(f,p)
    return jnp.sum(dfn*dpm-dpn*dfm)/dx

@jit
def tests(f,p,N,M,dx):
    return jnp.array([PB(f,p,N,M,dx),PB(f,p,N,M,dx,'no_mixing'),diffeo(f,p,N,M,dx),HJ(f,p,N,dx),HE(f,p,N,dx)])

def symbolic():
    # Check the scalar Schur complement and spatial conformal terms exactly
    F,X,Y,A,pc,pq=symbols=sp.symbols('F X Y A pc pq',real=True,nonzero=True)
    k=sp.Rational(3,2)/F
    DD=sp.Matrix([[1+k*X*X,k*X*Y],[k*X*Y,A+k*Y*Y]])
    vec=sp.Matrix([pc,pq])
    expr=sp.factor((vec.T*DD.inv()*vec)[0] - (pc**2+pq**2/A-k*(X*pc+Y*pq/A)**2/(1+k*(X*X+Y*Y/A))))
    assert expr==0,expr
    # Scalar-gradient + grav conformal cancellation reduces to identity for arbitrary F_x.
    N,W,Fx,sx,bx,wx,chi_x,q_x,eb,Nx=sp.symbols('N W Fx sx bx wx chi_x q_x eb Nx',real=True)
    r=Fx/(2*F)
    jordan=N*W*(F*(-sx*sx+bx*bx+eb*wx*wx/4)-2*Fx*sx+(chi_x**2+A*q_x**2)/2)-Nx*W*(2*F*sx+Fx)
    einstein=N*W*F*(-(sx+r)**2+bx*bx+eb*wx*wx/4+((chi_x**2+A*q_x**2)/F+sp.Rational(3,2)*Fx**2/F**2)/2)-(Nx*F*W+N*W*Fx/2)*2*(sx+r)
    assert sp.simplify(jordan-einstein)==0
    return {'two_scalar_schur_complement':'exact_zero','spatial_frame_identity':'exact_zero'}

def main():
    proof=symbolic();rows=[]
    for mode in ['standard','reverse_shear','strong_memory']:
        for n in [32,64,128,256,512]:
            f,p,N,M,dx=make_state(n,mode)
            bracket,wrong,target,hj,he=map(float,tests(f,p,N,M,dx))
            row={'mode':mode,'n':n,'dx':dx,'correct_bracket_residual':bracket-target,'omit_both_momentum_mixings':wrong-target,'frame_H_difference':he-hj}
            rows.append(row)
            print(mode,n,'correct:',bracket-target,'wrong:',wrong-target,'frame:',he-hj,flush=True)
    for mode in ['standard','reverse_shear','strong_memory']:
        r=[v for v in rows if v['mode']==mode]
        assert abs(r[-1]['correct_bracket_residual']) < abs(r[-2]['correct_bracket_residual'])/3.0
        assert abs(r[-1]['frame_H_difference']) < abs(r[-2]['frame_H_difference'])/3.0
        assert abs(r[-1]['omit_both_momentum_mixings'])>10*abs(r[-1]['correct_bracket_residual'])
    Fmin=2;Fmax=3.2
    ys=np.linspace(-2,2,501)
    F=2+1.2*np.tanh(ys/.45)**2
    fig,ax=plt.subplots(figsize=(7.8,4.5));ax.plot(ys,F,label='Tensor stiffness and inertia F(y)');ax.plot(ys,np.sqrt(F/F),label='Characteristic speed',linestyle='--')
    ax.set(xlabel='Lag y=q−χ',ylabel='Normalized response',title='Bounded lag-controlled tensor stiffness with matched inertia');ax.grid(alpha=.2);ax.legend();fig.tight_layout();fig.savefig(BASE/'lag_hardening_matched_cone_v28.png',dpi=160);plt.close(fig)
    with open(BASE/'lag_hardening_brackets_v28.csv','w',newline='') as out:
        wr=csv.DictWriter(out,list(rows[0]));wr.writeheader();wr.writerows(rows)
    summary={'symbolic':proof,'hardening_bounds':{'F_min':Fmin,'F_sup':Fmax,'F_at_y0':float(F[250])},'rows':rows,'warnings':['Both scalar canonical momenta are mixed because F depends on q and chi','No dissipative memory, y is reversible relative field','EH scalar-tensor structure assumed, not emergent']}
    (BASE/'lag_hardening_audit_v28.json').write_text(json.dumps(summary,indent=2,ensure_ascii=False)+'\n')
    print('BOUNDED STIFFENING V28 PASS',flush=True)
if __name__=='__main__':main()
