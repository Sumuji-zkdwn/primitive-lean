#!/usr/bin/env python3
"""Finite numerical audit of exact nonlinearly cross-polarized Rosen wave with two null scalars.
Uses direct 2x2 matrix derivatives, no pre-substitution of constraint cancellations.
"""
from pathlib import Path
import csv,json,math
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
ROOT=Path(__file__).resolve().parent

def go():
    G=.03; sigma=.07; p=.33; k=.30
    O=math.sqrt(k*k*math.sinh(2*p)**2+8*math.pi*G*sigma*sigma)
    D=np.diag([np.exp(2*p),np.exp(-2*p)])
    A=np.array([[0.,-1.],[1.,0.]])
    D1=A@D-D@A
    D2=A@D1-D1@A
    out=[]
    for u in np.linspace(-3,3,601):
        th=k*u
        R=np.array([[math.cos(th),-math.sin(th)],[math.sin(th),math.cos(th)]])
        b=math.log(math.cos(O*u));bp=-O*math.tan(O*u);bpp=-O*O/math.cos(O*u)**2
        M=R@D@R.T; M1=k*R@D1@R.T; M2=k*k*R@D2@R.T
        w=math.exp(2*b)
        H=w*M
        Hu=w*(2*bp*M+M1)
        Huu=w*((2*bpp+4*bp*bp)*M+4*bp*M1+M2)
        hi=np.linalg.inv(H)
        C=hi@Hu
        Ruu=-.5*np.trace(hi@Huu)+.25*np.trace(C@C)
        # ADM t-x split: gamma_xx=1, gamma_AB=H, lapse 1, shift 0.
        U=-C   # because u=t-x
        Ux=hi@Huu-C@C  # derivative_x U = derivative_u C
        R3=-np.trace(Ux)-.25*np.trace(U)**2-.25*np.trace(U@U)
        K=.5*C
        Kscalar=np.trace(K)
        Hcon=R3+Kscalar*Kscalar-np.trace(K@K)-16*math.pi*G*2*sigma*sigma
        # 3+1 momentum equation with K=+(1/2)d_t spatial metric.
        # Momentum = D_jK^j_x - d_x K = -tr(Gamma_trans K_trans) + d_u tr(K).
        # Gamma_trans = (1/2) H^-1 H_x = -(1/2) C.
        # d_u tr(K) = (1/2)tr(H^-1 H_uu-C²).
        momentum=.25*np.trace(C@C)+.5*np.trace(hi@Huu-C@C)
        momentum_res=momentum-8*math.pi*G*(-2*sigma*sigma)
        hplus=(H[0,0]-H[1,1])/(2*w)
        hcross=H[0,1]/w
        out.append([u,H[0,0],H[0,1],H[1,1],hplus,hcross,Ruu,Ruu-16*math.pi*G*sigma*sigma,R3,Hcon,momentum_res,b])
    arr=np.array(out)
    assert np.max(np.abs(arr[:,7]))<1e-12, np.max(np.abs(arr[:,7]))
    assert np.max(np.abs(arr[:,9]))<1e-12, np.max(np.abs(arr[:,9]))
    assert np.max(np.abs(arr[:,10]))<1e-12, np.max(np.abs(arr[:,10]))
    assert max(abs(arr[:,4]))>.1 and max(abs(arr[:,5]))>.1
    cols=['u','H_yy','H_yz','H_zz','plus_pol_normalized','cross_pol_normalized','Ruu','Ruu_minus_8piG_Tuu','R3','Hamiltonian_constraint','Momentum_constraint','b']
    with (ROOT/'cross_polarized_exact_wave_v23.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(cols);w.writerows(out)
    fig,ax=plt.subplots(2,1,figsize=(8,7),sharex=True)
    ax[0].plot(arr[:,0],arr[:,4],label='Plus polarization')
    ax[0].plot(arr[:,0],arr[:,5],label='Cross polarization')
    ax[0].set_ylabel('Normalized transverse metric');ax[0].legend()
    ax[1].plot(arr[:,0],np.maximum(np.abs(arr[:,7]),1e-18),label='4D Ricci residual')
    ax[1].plot(arr[:,0],np.maximum(np.abs(arr[:,9]),1e-18),label='Hamiltonian constraint')
    ax[1].plot(arr[:,0],np.maximum(np.abs(arr[:,10]),1e-18),label='Momentum constraint')
    ax[1].set_yscale('log');ax[1].set(xlabel='Retarded coordinate u=t-x',ylabel='Absolute residual')
    ax[1].legend(fontsize=8);ax[1].grid(alpha=.25)
    fig.tight_layout();fig.savefig(ROOT/'two_polarization_exact_wave_v23.png',dpi=170);plt.close(fig)
    summary={'G':G,'sigma':sigma,'polarization_amplitude_p':p,'rotation_wavenumber_k':k,'Omega':O,
             'max_4D_Ricci_residual':float(np.max(np.abs(arr[:,7]))),
             'max_ADM_Hamiltonian_residual':float(np.max(np.abs(arr[:,9]))),
             'max_ADM_momentum_residual':float(np.max(np.abs(arr[:,10]))),
             'max_plus':float(np.max(np.abs(arr[:,4]))),'max_cross':float(np.max(np.abs(arr[:,5]))),
             'lag_field':0.0,'gravitational_dynamics_borrowed_from_GR':True}
    (ROOT/'crossed_wave_audit_v23.json').write_text(json.dumps(summary,indent=2))
    print(json.dumps(summary,indent=2))

if __name__=='__main__':go()
