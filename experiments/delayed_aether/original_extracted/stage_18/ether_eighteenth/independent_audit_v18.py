#!/usr/bin/env python3
"""Independent checks of v18 computations; includes direct finite differences.
No external data or hidden prior result needed.
"""
import numpy as np,csv,json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
from verify_v18 import LAM,G,make_grid,make_kernel_fft,newton_energy,profile,density,radial_pieces,exact_matter
from collective_mode_v18 import collective_inertia
from constraint_v18 import iterate
OUT=Path(__file__).resolve().parent

def fval(r):
  a=1.15*np.exp(-(r*r)/(2*3.**2))
  f=2*np.arctan2(a,r)
  u=np.clip((r-9.)/3.,0,1)
  t=1-10*u**3+15*u**4-6*u**5
  return f*t if r<12 else 0.

def fields(x,s):
  y=np.array([np.exp(s)*x[0],np.exp(-s)*x[1],x[2]])
  r=np.linalg.norm(y);f=fval(r)
  q=np.r_[np.cos(f),np.sin(f)*y/r]
  return q,np.cos(f)

def density_inertia_point_from_fd(x,s=0.1,h=2e-5):
  q,chi=fields(x,s)
  g=[];gc=[]
  for i in range(3):
    ex=np.zeros(3);ex[i]=h
    qp,cp=fields(x+ex,s)
    qm,cm=fields(x-ex,s)
    g.append((qp-qm)/(2*h));gc.append((cp-cm)/(2*h))
  qplus,cp=fields(x,s+h);qminus,cm=fields(x,s-h)
  qt=(qplus-qminus)/(2*h);ct=(cp-cm)/(2*h)
  Gmat=np.array([[np.dot(g[i],g[j]) for j in range(3)] for i in range(3)])
  tr=np.trace(Gmat);tr2=np.sum(Gmat*Gmat)
  E2=.5*(tr+np.sum(np.array(gc)**2))
  E4=.25*LAM*(tr*tr-tr2)
  I2=np.dot(qt,qt)+ct*ct
  I4=LAM*(np.dot(qt,qt)*tr-sum(np.dot(qt,gi)**2 for gi in g))
  return E2,E4,I2,I4

def density_inertia_point_formula(x,s):
  # evaluate against model formula, no finite differences
  dx,dy=np.exp(s),np.exp(-s)
  y=np.array([dx*x[0],dy*x[1],x[2]])
  r=np.linalg.norm(y)
  a,b,cp2,A,V,lag=profile(np.array([r]));a=float(a[0]);b=float(b[0]);cp2=float(cp2[0])
  n=y/r;d2=np.array([dx*dx,dy*dy,1.])
  t1=np.dot(d2,n*n);t2=np.dot(d2*d2,n*n)
  tr=b*np.sum(d2)+(a-b)*t1
  tr2=b*b*np.dot(d2,d2)+2*b*(a-b)*t2+(a-b)**2*t1*t1
  E2=.5*(tr+cp2*t1)
  E4=.25*LAM*(tr*tr-tr2)
  w=np.array([y[0],-y[1],0.]);nw=np.dot(n,w)
  qn=b*np.dot(w,w)+(a-b)*nw*nw
  I2=qn+cp2*nw*nw
  gw=b*w+(a-b)*n*nw
  I4=LAM*(qn*tr-np.dot(gw*d2,gw))
  return E2,E4,I2,I4

def test_analytic_derivatives():
  rng=np.random.default_rng(1818)
  errs=[]
  for _ in range(120):
    x=rng.normal(size=3);x=x/np.linalg.norm(x)*rng.uniform(.25,8.5)
    s=rng.uniform(-.23,.23)
    actual=np.array(density_inertia_point_from_fd(x,s))
    ref=np.array(density_inertia_point_formula(x,s))
    errs.append(float(np.max(np.abs(actual-ref)/(1+np.abs(ref)))))
  assert max(errs)<1e-7
  return max(errs)

def test_fft_convolution():
  rng=np.random.default_rng(1234)
  n=5;h=.4;rho=rng.random((n,n,n))
  Khat=make_kernel_fft(n,h)
  fast=newton_energy(rho,h,Khat)
  coords=np.array(np.meshgrid(*[h*np.arange(n)]*3,indexing='ij')).reshape(3,-1).T
  diff=coords[:,None,:]-coords[None,:,:]
  d=np.linalg.norm(diff,axis=-1)
  kernel=np.divide(1.,d,out=np.zeros_like(d),where=d>0)
  np.fill_diagonal(kernel,2.380077363979553/h)
  direct=-.5*G*h**6*float(rho.ravel()@kernel@rho.ravel())
  err=abs(fast-direct)
  assert err<1e-11
  return err

def test_boundary_integral():
  datum,grid,psi,S,terms,hist=iterate(n=81,s=.16)
  n,L,h,xx,X,Y,Z=grid
  d=[]
  for point in [(15.,0.,0.),(0.,15.,0.),(0.,0.,15.),(15.,15.,15.)]:
    dx=X-point[0];dy=Y-point[1];dz=Z-point[2]
    rr=np.sqrt(dx*dx+dy*dy+dz*dz)
    K=np.divide(1.,rr,out=np.zeros_like(rr),where=rr>0)
    # density vanishes exactly at the test boundary sample cells
    direct=1+G*.5*h**3*np.sum(S*K)
    inds=tuple(int(np.argmin(abs(xx-p))) for p in point)
    from_bdy=float(psi[inds])
    d.append(dict(point=point,psi_boundary=from_bdy,psi_direct=direct,
                  abs_diff=abs(direct-from_bdy),rel_to_psi_minus_one=abs(direct-from_bdy)/(from_bdy-1)))
  return d

def main():
  gd=test_analytic_derivatives()
  fft=test_fft_convolution()
  bdy=test_boundary_integral()
  affine=list(csv.DictReader(open(OUT/'affine_gravity_energy.csv')))
  max_affine=max(abs(float(row['Emat'])-float(row['Emat_exact'])) for row in affine if int(row['n'])==96)
  adm=list(csv.DictReader(open(OUT/'non_spherical_adm_initial_data.csv')))
  symmetry=[]
  for n in ('41','61'):
    pos=next(row for row in adm if row['n']==n and row['s']=='0.16')
    neg=next(row for row in adm if row['n']==n and row['s']=='-0.16')
    symmetry.append(abs(float(pos['ADM_mass'])-float(neg['ADM_mass'])))
  hess=list(csv.DictReader(open(OUT/'nonaffine_hessian.csv')))
  min_hessian=min(float(row['centered_second_derivative']) for row in hess)
  out={
    'analytic_vs_finite_difference_density_and_shape_inertia_max_relative_err':gd,
    'zero_padded_FFT_Newton_energy_vs_direct_125body_absolute_err':fft,
    'max_3d_affine_static_energy_vs_exact_formula_absolute_err':max_affine,
    'ADM_s_positive_negative_symmetry_mass_difference':symmetry,
    'nonaffine_sample_min_centered_hessian':min_hessian,
    'boundary_multipole_approximation_vs_direct_green_integral':bdy,
    'analytic_nonaffine_diffeomorphism_sufficient_condition':'||DF-I||_op <= |eps| * 2 exp(-1/2) < 1 if |eps|<exp(1/2)/2 ~0.82436',
    'known_limitations':'finite grids, static non-spherical initial data, fixed-shape 1DOF dynamics; not a 3D full Einstein time evolution nor proof of arbitrary-mode stability'
  }
  assert max(symmetry)<1e-9
  assert max_affine<2e-6
  assert min_hessian>0
  with (OUT/'independent_audit_v18.json').open('w') as f:json.dump(out,f,indent=2,ensure_ascii=False)
  print(json.dumps(out,indent=2))

if __name__=='__main__':main()
