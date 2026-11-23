#!/usr/bin/env python3
"""4D 1->5 Regge subdivision: exact Hessian + independent geometric checks.
Only the Euclidean Regge action on ONE 4-simplex is studied, not graviton dynamics.
"""
import itertools, json, csv
from pathlib import Path
import numpy as np
import sympy as sp
from numpy.linalg import inv, eigvalsh, norm

OUT=Path(__file__).resolve().parent
OUT.mkdir(parents=True,exist_ok=True)
OUTER=tuple(range(5))
PAIRS=tuple(itertools.combinations(OUTER,2))
TRIPLES=tuple(itertools.combinations(OUTER,3))
SUBSETS={omit:tuple(i for i in OUTER if i!=omit) for omit in OUTER}
R0=float(np.sqrt(2/5))

# A 4-simplex with 4 outer vertices and one central vertex at v0.
# Its four relative vectors have Gram_{ij}=(l_0i^2+l_0j^2-l_ij^2)/2.
# Face normals are gradients of barycentric coordinates; their Gram matrix
# provides Euclidean *interior* dihedral angles, no embeddings required.
def one_subsimplex(r, omit):
    others=SUBSETS[omit]
    rr=r[list(others)]
    G=(rr[:,None]**2+rr[None,:]**2-1)/2
    np.fill_diagonal(G,rr**2)
    lamb=eigvalsh(G)
    if np.min(lamb)<=0:
        raise ValueError('degenerate 4-simplex')
    V=inv(G)
    C=np.empty((5,5))
    C[1:,1:]=V
    C[0,1:]=-np.sum(V,axis=0)
    C[1:,0]=C[0,1:]
    C[0,0]=np.sum(V)
    # theta[p,q] at codimension-2 triangle opposite vertices p,q.
    T=np.zeros((5,5))
    for p in range(5):
        for q in range(p+1,5):
            cs=-C[p,q]/np.sqrt(C[p,p]*C[q,q])
            T[p,q]=T[q,p]=np.arccos(np.clip(cs,-1,1))
    return others, T

def deficit_and_boundary(r):
    sub={omit:one_subsimplex(r,omit) for omit in OUTER}
    de=np.zeros(len(PAIRS))
    for k,(a,b) in enumerate(PAIRS):
        theta=0.
        for omit in OUTER:
            if omit in (a,b):
                continue
            o,T=sub[omit]
            c,d=(x for x in o if x not in (a,b))
            theta+=T[1+o.index(c),1+o.index(d)]
        de[k]=2*np.pi-theta
    be=[]
    for tri in TRIPLES:
        theta=0.
        for omit in OUTER:
            if omit in tri:
                continue
            o,T=sub[omit]
            other=next(v for v in o if v not in tri)
            theta+=T[0,1+o.index(other)]
        be.append(np.pi-theta)
    return de, np.asarray(be)

def triangle_area_and_deriv(a,b):
    # sides (a,b,1)
    A=.5*np.sqrt(a*a*b*b-((a*a+b*b-1)/2)**2)
    da=a*(b*b-a*a+1)/(8*A)
    db=b*(a*a-b*b+1)/(8*A)
    return A,da,db

def action(r):
    deficits,bdy=deficit_and_boundary(r)
    inter=sum(triangle_area_and_deriv(r[a],r[b])[0]*d
              for (a,b),d in zip(PAIRS,deficits))
    boundary=np.sqrt(3)/4*np.sum(bdy)
    return inter+boundary

def regge_gradient(r):
    # Schlaefli identity cancels all dihedral variations for fixed boundary lengths.
    de,_=deficit_and_boundary(r)
    g=np.zeros(5)
    for (a,b),d in zip(PAIRS,de):
        _,da,db=triangle_area_and_deriv(r[a],r[b])
        g[a]+=da*d
        g[b]+=db*d
    return g

def numeric_hessian(r, step=2e-5):
    H=np.zeros((5,5))
    for i in OUTER:
        v=np.zeros(5);v[i]=step
        H[:,i]=(regge_gradient(r+v)-regge_gradient(r-v))/(2*step)
    return (H+H.T)/2

def outer_coordinates():
    # Regular 4-simplex, side length 1, v0=(0,0,0,0).
    gram=np.full((4,4),.5)
    np.fill_diagonal(gram,1.)
    V=np.linalg.cholesky(gram).T
    points=np.zeros((5,4))
    points[1:]=V.T
    return points

def check():
    pts=outer_coordinates()
    center=pts.mean(axis=0)
    r=np.linalg.norm(pts-center,axis=1)
    assert np.max(abs(r-R0))<1e-14
    de,bd=deficit_and_boundary(r)
    baseline_grad=regge_gradient(r)
    H=numeric_hessian(r)
    Hexact=8*np.sqrt(5)*np.ones((5,5))
    eig=eigvalsh(H)
    # A gauge-preserving alternative to raw-edge memory: store deficit-angle history.
    # Both examples below are STATIC Hessians at memory equilibrium, not yet time dynamics.
    h=2e-5
    D=np.column_stack([(deficit_and_boundary(r+h*np.eye(5)[i])[0]-
                        deficit_and_boundary(r-h*np.eye(5)[i])[0])/(2*h)
                       for i in OUTER])
    Dexact=6*np.sqrt(10/3)*np.ones((10,5))
    eta=.001
    Hcurvature_memory=Hexact+eta*D.T@D
    Hedge_memory=Hexact+np.eye(5)
    J=(center[None,:]-pts)/r[:,None]
    # All infinitesimal vertex movements preserve flatness.
    assert np.linalg.matrix_rank(J,tol=1e-9)==4
    rng=np.random.default_rng(20261123)
    finite_shifts=[]
    for _ in range(48):
        shift=.025*rng.normal(size=4)
        trial=np.linalg.norm(pts-(center+shift),axis=1)
        # A displacement of the interior vertex must stay inside outer simplex
        # (these .025 shifts do, since center has generous margin).
        d,_=deficit_and_boundary(trial)
        finite_shifts.append((np.max(abs(d)),abs(action(trial)-action(r))))
    # Test at a non-centered but still flat interior vertex. Four null modes
    # must persist without the artificial all-edges-equal symmetry.
    displaced_center=center+np.array([.024,-.012,.017,-.019])
    displaced_r=np.linalg.norm(pts-displaced_center,axis=1)
    H_displaced=numeric_hessian(displaced_r)
    J_displaced=(displaced_center[None,:]-pts)/displaced_r[:,None]
    displaced_eig=eigvalsh(H_displaced)
    # Compare the action and the Schlaefli gradient independently.
    p=np.array([.006,-.004,.001,.003,-.002])
    test=r+p
    h=1e-5
    grad_by_action=np.array([(action(test+np.eye(5)[i]*h)-action(test-np.eye(5)[i]*h))/(2*h) for i in OUTER])
    # Breaking flatness uniformly excites one curvature mode.
    delta=.002
    uniform=r+delta*np.ones(5)
    deformed_deficits,_=deficit_and_boundary(uniform)
    Ecurved=action(uniform)-action(r)
    quadratic_prediction=.5*float((uniform-r)@Hexact@(uniform-r))
    # Ordinary spring elastic energy E=1/2 sum_i (r_i-r_i0)^2.
    # Its Hessian is I_5 and it penalizes the four vertex displacements.
    # Regge local Hessian = all-ones with rank 1 and four zero modes.
    rows=[]
    for n in [1,2,3,4]:
        v=J[:,n-1]
        rows.append({'mode':f'flat vertex shift {n}',
                     'regge_quadratic_curvature':float(v@Hexact@v),
                     'spring_quadratic_curvature':float(v@v)})
    rows.append({'mode':'nonmetric radial length mode',
                 'regge_quadratic_curvature':float(np.ones(5)@Hexact@np.ones(5)/5),
                 'spring_quadratic_curvature':1.0})
    with open(OUT/'mode_comparison_v30.csv','w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
    results={
      'geometry':'five 4-simplices subdividing one regular 4-simplex, side length one, centered interior vertex',
      'internal_edges':5,'internal_triangles':10,'boundary_triangles':10,
      'radial_edge_length':R0,
      'baseline_interior_deficit_max_abs':float(max(abs(de))),
      'baseline_regge_gradient_max_abs':float(max(abs(baseline_grad))),
      'hessian_analytic_coefficient_per_entry':'8 sqrt(5)',
      'hessian_analytic_nonzero_eigenvalue':'40 sqrt(5)',
      'hessian_analytic_nonzero_eigenvalue_float':float(40*np.sqrt(5)),
      'hessian_numeric_eigenvalues':list(map(float,eig)),
      'hessian_numerical_max_abs_error':float(max(abs(H-Hexact).flat)),
      'hessian_gauge_null_residual_max_abs':float(max(abs(Hexact@J).flat)),
      'hessian_numerical_gauge_null_residual_max_abs':float(max(abs(H@J).flat)),
      'interior_shift_48_max_deficit':float(max(x[0] for x in finite_shifts)),
      'interior_shift_48_max_action_difference':float(max(x[1] for x in finite_shifts)),
      'displaced_flat_hessian_eigenvalues':list(map(float,displaced_eig)),
      'displaced_flat_gauge_null_residual_max_abs':float(np.max(np.abs(H_displaced@J_displaced))),
      'gradient_action_vs_schlaefli_max_abs_error':float(np.max(np.abs(grad_by_action-regge_gradient(test)))),
      'uniform_radius_shift':delta,
      'uniform_deficit_range':list(map(float,[min(deformed_deficits),max(deformed_deficits)])),
      'uniform_action_difference':float(Ecurved),
      'uniform_quadratic_prediction':float(quadratic_prediction),
      'ordinary_spring_hessian_eigenvalues':[1.0]*5,
      'deficit_jacobian_max_abs_error':float(np.max(abs(D-Dexact))),
      'deficit_jacobian_exact_entry':'6 sqrt(10/3)',
      'curvature_memory_eta':eta,
      'curvature_memory_analytic_hessian_entry':'8 sqrt(5) + 1200 eta',
      'curvature_memory_numerical_eigenvalues':list(map(float,eigvalsh(Hcurvature_memory))),
      'raw_edge_memory_numerical_eigenvalues':list(map(float,eigvalsh(Hedge_memory))),
      'statement':'4 zero modes are flat embedding vertex shifts, NOT four graviton modes. The sole nonzero mode is curvature. Regge action input is a discretized Einstein-Hilbert model, NOT emergent gravity.'
    }
    (OUT/'audit_v30.json').write_text(json.dumps(results,indent=2,ensure_ascii=False)+'\n')
    # scans (1d symmetry-breaking direction and flat gauge direction)
    rs=[]
    shift_dir=np.array([1.,0,0,0]);
    for amplitude in np.linspace(-.014,.035,41):
        curved=np.full(5,R0)+amplitude
        displaced=np.linalg.norm(pts-(center+amplitude*shift_dir),axis=1)
        rs.append({'parameter':amplitude,
                   'regge_uniform_delta_action':action(curved)-action(r),
                   'regge_flat_shift_delta_action':action(displaced)-action(r),
                   'spring_uniform_delta_energy':.5*norm(curved-r)**2,
                   'spring_flat_shift_delta_energy':.5*norm(displaced-r)**2})
    with open(OUT/'flat_vs_curved_v30.csv','w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rs[0]);w.writeheader();w.writerows(rs)
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    fig,axs=plt.subplots(1,2,figsize=(10,3.8))
    amp=np.array([s['parameter'] for s in rs])
    axs[0].plot(amp,[s['regge_uniform_delta_action'] for s in rs],label='Regge: uniform radial lengths')
    axs[0].plot(amp,[s['regge_flat_shift_delta_action'] for s in rs],label='Regge: flat vertex displacement')
    axs[0].plot(amp,[s['spring_flat_shift_delta_energy'] for s in rs],label='Spring: vertex displacement',linestyle='--')
    axs[0].set(xlabel='perturbation',ylabel='change in action / energy',title='Regge gauge direction vs spring stiffness')
    axs[0].legend(fontsize=7)
    axs[1].plot(np.arange(1,6),eig,'o',label='Regge numerical Hessian')
    axs[1].plot(np.arange(1,6),eigvalsh(Hcurvature_memory),'s',label='Regge + deficit memory')
    axs[1].plot(np.arange(1,6),eigvalsh(Hedge_memory),'x',label='Regge + raw edge memory')
    axs[1].axhline(0,linestyle=':',linewidth=.7)
    axs[1].set(xlabel='eigenvalue index',ylabel='eigenvalue',title='Four exact Regge null modes')
    axs[1].legend(fontsize=7)
    fig.tight_layout();fig.savefig(OUT/'regge_vs_elasticity_v30.png',dpi=175);plt.close(fig)
    # exact algebraic symbolic proof for all-ones Hessian coefficient
    x=sp.symbols('x',positive=True)
    t=x*x
    costheta=(2*t-1)/(2*(3*t-1))
    theta=sp.acos(costheta)
    deficit=2*sp.pi-3*theta
    triangle_area=sp.sqrt(4*x*x-1)/4
    # sum of gradient components for a symmetric radial move = 10 δ A'(x).
    # Since dS/dx =5 g_e, and H=c J, d²S/dx² =25 c.
    c=sp.simplify(sp.diff(triangle_area,x).subs(x,sp.sqrt(sp.Rational(2,5))) *
                    sp.diff(deficit,x).subs(x,sp.sqrt(sp.Rational(2,5)))*sp.Rational(10,25))
    symbolic={'radial_edge_x0':'sqrt(2/5)','theta_internal_at_x0':'2*pi/3',
              'dihedral_cosine_formula':str(costheta),'symbolic_hessian_entry':str(c),
              'assert_equals_8sqrt5':sp.simplify(c-8*sp.sqrt(5))==0}
    (OUT/'symbolic_certificate_v30.json').write_text(json.dumps(symbolic,indent=2)+'\n')
    assert symbolic['assert_equals_8sqrt5']
    assert results['hessian_numerical_max_abs_error']<2e-4
    assert results['deficit_jacobian_max_abs_error']<1e-4
    assert results['baseline_interior_deficit_max_abs']<1e-12
    assert results['gradient_action_vs_schlaefli_max_abs_error']<1e-7
    assert results['interior_shift_48_max_deficit']<1e-12
    assert results['interior_shift_48_max_action_difference']<1e-12
    assert np.max(abs(displaced_eig[:4]))<2e-5
    assert results['displaced_flat_gauge_null_residual_max_abs']<2e-5
    print(json.dumps(results,ensure_ascii=False,indent=2))
if __name__=='__main__':
    check()
