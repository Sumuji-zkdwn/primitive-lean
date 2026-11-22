#!/usr/bin/env python3
"""Independent finite/rational validation, separate from verify_v20 implementation.
Runs 4D tensor ranks across exact wavevectors and the universal source Ward test.
"""
import json
from pathlib import Path
import numpy as np
from scipy.integrate import solve_ivp, trapezoid
from sympy import Matrix, diag, eye, zeros

OUT=Path(__file__).resolve().parent
eta=diag(-1,1,1,1)
slots=[(i,j) for i in range(4) for j in range(i,4)]
def symflat(a):
    return Matrix([a[i,j] for i,j in slots])
def fp_operator(k,h):
    # Overall normalization convention independent of main implementation.
    ku=eta*k
    sq=(k.T*ku)[0]
    v=h*ku
    tr=(eta*h).trace()
    return (2*sq*h-2*(k*v.T+v*k.T) +2*(k*k.T*tr+eta*(ku.T*v)[0])
            -2*eta*sq*tr)
def rank_test(kdata):
    k=Matrix(kdata)
    operator=[]
    gauges=[]
    for i,j in slots:
        h=zeros(4)
        h[i,j]=1
        h[j,i]=1
        operator.append(symflat(fp_operator(k,h)))
    for i in range(4):
        xi=eye(4).col(i)
        gauges.append(symflat(k*xi.T+xi*k.T))
    A=Matrix.hstack(*operator)
    G=Matrix.hstack(*gauges)
    assert A*G==zeros(10,4)
    return {'k':list(map(int,kdata)), 'k2':int((k.T*eta*k)[0]),
            'rank_operator':int(A.rank()), 'gauge_rank':int(G.rank()),
            'physical_plane_wave_dimension':10-int(A.rank())-int(G.rank())}
def coupled_numerical(k,lam,y0,T=12):
    def f(t,y):
        q,z,v,w=y
        F=k*(q-z)+lam*(q-z)**3
        return [v,w,-F,F]
    tt=np.linspace(0,T,2401)
    sol=solve_ivp(f,(0,T),y0,method='DOP853',t_eval=tt,rtol=1e-12,atol=1e-13)
    assert sol.success
    q,z,v,w=sol.y
    delta=q-z
    F=k*delta+lam*delta**3
    Kq=.5*v**2; Kz=.5*w**2; V=.5*k*delta**2+.25*lam*delta**4
    Et=Kq+Kz+V
    total_error=float(np.max(np.abs(Et-Et[0]))/Et[0])
    assert total_error<1e-9,total_error
    # Gauge parameter ξ vanishes at endpoints, so δS = ∫ ξ' J = - ∫ ξ Jdot.
    midpoint=3.8
    width=0.8
    window=tt*(T-tt)/T**2
    dw=(T-2*tt)/T**2
    bell=np.exp(-((tt-midpoint)/width)**2)
    xi=window*bell
    xi_dot=dw*bell+window*bell*(-2*(tt-midpoint)/width**2)
    def variation(weights):
        cq,cz,cv=weights
        J=cq*Kq+cz*Kz+cv*V
        Jdot=F*((cv-cq)*v+(cz-cv)*w)
        int_by_parts=trapezoid(xi_dot*J,tt)
        int_source=-trapezoid(xi*Jdot,tt)
        return {'gauge_variation_integral':float(int_by_parts),
                'integration_by_parts_rhs':float(int_source),
                'int_by_parts_difference':float(abs(int_by_parts-int_source)),
                'max_abs_source_divergence':float(np.max(np.abs(Jdot)))}
    return {'k':float(k),'lam':float(lam),'initial':list(map(float,y0)),
            'max_relative_total_energy_drift':total_error,
            'total_source':variation((1.,1.,1.)),
            'q_only_source':variation((1.,0.,0.)),
            'unequal_source':variation((1.,2.,1.))}

def main():
    nulls=[(-1,0,0,1),(-5,3,4,0),(-13,3,4,12),(-1,1,0,0)]
    notnulls=[(1,0,0,0),(0,1,0,0),(2,0,1,0)]
    ranks=[rank_test(x) for x in nulls+notnulls]
    assert all(z['physical_plane_wave_dimension']==2 for z in ranks[:len(nulls)])
    assert all(z['physical_plane_wave_dimension']==0 for z in ranks[len(nulls):])
    states=[(.9,.35,[1.1,-.25,.4,-.15]), (1.5,0,[.7,-.6,-.3,.45]),
            (.3,.85,[1.35,.4,.15,-.5])]
    numerical=[coupled_numerical(*x) for x in states]
    for n in numerical:
        assert abs(n['total_source']['gauge_variation_integral'])<2e-8
        assert n['q_only_source']['max_abs_source_divergence']>.01
        assert n['q_only_source']['int_by_parts_difference']<2e-7
    audit={'null_and_nonnul_wavevectors':ranks,'independent_initial_state_and_coupling_cases':numerical,
           'interpretation':'On-shell total stress conserved in this toy model; partial stresses cannot consistently couple alone to the same linear massless spin-2 gauge symmetry.'}
    (OUT/'independent_audit_v20.json').write_text(json.dumps(audit,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps(audit,indent=2,ensure_ascii=False))
if __name__=='__main__':main()
