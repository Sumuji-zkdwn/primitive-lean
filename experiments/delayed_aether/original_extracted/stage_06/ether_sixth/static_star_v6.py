#!/usr/bin/env python3
"""Static pressure-supported incompressible fluid in V6 scalar-disformal toy.

This solves the *toy's own* scalar equation + hydrostatic equilibrium,
NOT the Einstein TOV equations. Coordinates are isotropic; G=c=R=1.
"""
from pathlib import Path
import csv,json
import numpy as np
from scipy.integrate import solve_bvp,simpson
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
OUT=Path(__file__).resolve().parent

def solve_star(rho, R=1.,tol=4e-8):
    eps=1e-4*R
    rr=np.linspace(eps,R,400)
    m_newton=4*np.pi*rho*R**3/3
    U0=2*np.pi*rho*(R*R-rr*rr/3)
    DU0=-4*np.pi*rho*rr/3
    P0=rho*np.maximum(U0-m_newton/R,0.)
    initial=np.vstack([U0,DU0,P0])
    def f(x,y):
        U,DU,P=y
        return np.vstack([DU,-2*DU/x -4*np.pi*np.exp(2*U)*(rho+3*P), (rho+P)*DU])
    def bc(ya,yb):
        Uc,DUc,Pc=ya
        return np.array([DUc+(4*np.pi/3)*eps*np.exp(2*Uc)*(rho+3*Pc),
                         yb[2],yb[0]+R*yb[1]])
    sol=solve_bvp(f,bc,rr,initial,tol=tol,max_nodes=6000)
    if sol.status!=0: return dict(rho=rho,status='NO_CONVERGENCE',message=sol.message),None
    x=np.linspace(eps,R,1600)
    U,DU,P=sol.sol(x)
    mass=-R*R*DU[-1]
    grav_source=4*np.pi*x*x*np.exp(2*U)*(rho+3*P)
    mass_integrated=simpson(grav_source,x=x)
    # central omitted volume 4pi*r^3/3*(rho+3P)*exp(2U)
    mass_integrated+=(4*np.pi/3)*eps**3*np.exp(2*U[0])*(rho+3*P[0])
    P_from_hydro=rho*np.expm1(U-U[-1])
    residual_hydro=float(np.max(np.abs(P-P_from_hydro)))
    rel_mass_err=abs(mass_integrated-mass)/mass
    assert np.max(np.abs(P))>0 and P.min()>-1e-8
    assert residual_hydro<5e-8,(rho,residual_hydro)
    assert rel_mass_err<3e-6,(rho,rel_mass_err)
    assert abs(U[-1]-mass/R)<1e-9
    row={'rho':rho,'status':'CONVERGED','R':R,'mass_from_boundary':mass,
         'newton_mass_4piR3rho_over3':m_newton,'amplification_mass_ratio':mass/m_newton,
         'mass_from_source_integral':mass_integrated,'relative_mass_balance_err':rel_mass_err,
         'central_U':U[0], 'surface_U':U[-1], 'central_pressure':P[0],
         'max_hydro_integral_residual':residual_hydro,
         'max_collocation_ODE_residual':float(np.max(sol.rms_residuals)),
         'num_mesh_nodes':sol.x.size}
    profile={'r':x,'U':U,'dUdr':DU,'pressure':P,'grav_source':grav_source}
    return row,profile

def main():
    values=[.002,.005,.01,.015,.02,.024,.026,.028]
    rows=[]; profiles={}
    for rho in values:
        row,profile=solve_star(rho)
        rows.append(row)
        print(rho,row.get('status'),row.get('mass_from_boundary'),row.get('amplification_mass_ratio'),row.get('relative_mass_balance_err'))
        if profile is not None: profiles[rho]=profile
    with (OUT/'static_fluid_stars.csv').open('w',newline='') as fh:
        fields=['rho','status','R','mass_from_boundary','newton_mass_4piR3rho_over3',
                'amplification_mass_ratio','mass_from_source_integral','relative_mass_balance_err',
                'central_U','surface_U','central_pressure','max_hydro_integral_residual',
                'max_collocation_ODE_residual','num_mesh_nodes','message']
        writer=csv.DictWriter(fh,fieldnames=fields)
        writer.writeheader();writer.writerows(rows)
    fig,ax=plt.subplots(figsize=(8.4,4.7))
    for rho in [.002,.01,.02,.026]:
        p=profiles[rho]
        ax.plot(p['r'],p['U'],label=f'rho={rho:g}')
    ax.set(xlabel='Isotropic radius r (star surface at 1)',ylabel='U(r)',title='Self-consistent toy scalar potential inside fluid stars')
    ax.grid(alpha=.25);ax.legend();fig.tight_layout();fig.savefig(OUT/'star_potential.png',dpi=155);plt.close(fig)
    fig,ax=plt.subplots(figsize=(8.4,4.7))
    for rho in [.002,.01,.02,.026]:
        p=profiles[rho]
        ax.plot(p['r'],p['pressure'],label=f'rho={rho:g}')
    ax.set(xlabel='Isotropic radius r',ylabel='Fluid pressure p(r)',title='Hydrostatic support, p(R)=0')
    ax.grid(alpha=.25);ax.legend();fig.tight_layout();fig.savefig(OUT/'star_pressure.png',dpi=155);plt.close(fig)
    (OUT/'static_star_results.json').write_text(json.dumps(rows,indent=2)+'\n')
    assert sum(row['status']=='CONVERGED' for row in rows)>=6
if __name__=='__main__': main()
