#!/usr/bin/env python3
"""Witness topology loss in interpolated unit-vector lattice field.
Target: n=12, fixed boundary, topological degree through a tetra whose
unnormalized affine q interpolation can reach zero. This is a lattice defect,
not evidence of true continuous Skyrmion destruction.
"""
import json, numpy as np
from scipy.optimize import brentq
from verify_v12 import Model
from verify_v11 import degree_preimage
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def main():
 m=Model(n=12)
 h=.001
 state=m.prepare()
 previous_q=state[0].copy();previous_charge=m.degree(previous_q)
 crossing=None
 for step in range(1,351):
    state=m.step(state,h)
    if step < 210 or step % 1:continue
    q=state[0]
    charge=m.degree(q)
    if charge!=previous_charge:
        crossing=(step-1,step,previous_q.copy(),q.copy(),previous_charge,charge)
        break
    previous_q=q.copy();previous_charge=charge
 if crossing is None:
    raise AssertionError('No topology change found in range')
 s0,s1,q0,q1,Q0,Q1=crossing
 v0=q0.reshape(-1,4)[m.tets]
 v1=q1.reshape(-1,4)[m.tets]
 d0=np.linalg.det(v0)
 d1=np.linalg.det(v1)
 indices=np.nonzero(d0*d1<0)[0]
 # Find an origin-containing tetrahedron exactly at an interpolated determinant root.
 candidates=[]
 for i in indices:
    A,B=v0[i],v1[i]
    normvertices=lambda alpha: (lambda W: W/np.linalg.norm(W,axis=-1,keepdims=True))((1-alpha)*A+alpha*B)
    f=lambda alpha:np.linalg.det(normvertices(alpha))
    if f(0)*f(1)>0:continue
    try:root=brentq(f,0,1,xtol=1e-14)
    except ValueError:continue
    C=normvertices(root)
    # at singular C, find nullvector of C.T using SVD; enforce nonnegative barycentric.
    u,s,vh=np.linalg.svd(C.T)
    lam=vh[-1]
    if abs(np.sum(lam))<1e-7:continue
    lam=lam/np.sum(lam)
    residual=float(np.linalg.norm(lam@C))
    if np.all(lam>=-1.e-8) and np.all(lam<=1+1e-8) and residual<1e-8:
        candidates.append({'tet_id':int(i),'mix_parameter':float(root),'time_approx':float((s0+root)*h),
                           'barycentric':lam.tolist(),'residual':residual,
                           'smallest_singular':float(s[-1]),'tet_indices':m.tets[i].tolist(),
                           'center':np.einsum('i,ij->j',lam,m.coords[m.tets[i]]).tolist()})
 result={'step_pre':s0,'step_post':s1,'time_pre':s0*h,'time_post':s1*h,
         'charge_pre':Q0,'charge_post':Q1,'tets_with_strict_determinant_sign_change':int(len(indices)),
         'witness_count':len(candidates),'witnesses':candidates[:8],
         'interpretation':'normalized linear interpolation of vertex q between consecutive configurations; at the witness time the spatial affine field in one tetrahedron contains 0, so normalized spatial interpolation fails although vertex vectors remain unit length'}
 (ROOT/'topology_slip_witness.json').write_text(json.dumps(result,indent=2,ensure_ascii=False))
 print(json.dumps(result,indent=2))
 if not candidates:
    raise RuntimeError('Degree changed but no affine-interpolation singularity witness found; inspect reconstruction algorithm')

if __name__=='__main__':main()
