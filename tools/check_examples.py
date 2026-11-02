"""Independent numerical checks. These are not general mathematical proofs."""
from pathlib import Path
from datetime import datetime, timezone
import json
import numpy as np

ROOT=Path(__file__).resolve().parents[1]

def run():
    nodes,weights=np.polynomial.legendre.leggauss(128)
    s=(nodes+1)/2; weights=weights/2
    integ=lambda f:float(np.dot(weights,f))
    theta=.2+.4*s+.3*s*s+.2*np.sin(np.pi*s)
    kappa=.4+.6*s+.2*np.pi*np.cos(np.pi*s)
    eta=s*(1-s)*(1+.2*s)
    etaprime=1-1.6*s-.6*s*s
    density=lambda q:q**4/4+q*q/2+.3*q
    densityprime=lambda q:q**3+q+.3
    expected=integ(densityprime(kappa)*etaprime)
    hx=-integ(np.sin(theta)*eta); hy=integ(np.cos(theta)*eta)
    checks=[]
    for h in (1e-3,1e-4,1e-5):
        energy=(integ(density(kappa+h*etaprime))-integ(density(kappa-h*etaprime)))/(2*h)
        dx=(integ(np.cos(theta+h*eta))-integ(np.cos(theta-h*eta)))/(2*h)
        dy=(integ(np.sin(theta+h*eta))-integ(np.sin(theta-h*eta)))/(2*h)
        errors=[abs(energy-expected),abs(dx-hx),abs(dy-hy)]
        checks.append(dict(name='first_variation',step=h,absolute_errors=errors,
            tolerance=max(2e-8,2*h*h),passed=max(errors)<max(2e-8,2*h*h)))
    # Fixed-end angle variation at a straight line: both position derivatives
    # vanish, but the exact horizontal displacement changes at nonzero t.
    e=s*(1-s)*(2*s-1)
    first_x=0.; first_y=integ(e)
    changed=integ(np.cos(.5*e))-1
    checks.append(dict(name='linearized_does_not_mean_exact_constraint',
        first_derivatives=[first_x,first_y],horizontal_change=changed,
        passed=abs(first_y)<1e-14 and changed < -1e-5))
    a,b=.7,-.2
    actual_shift=integ(density(kappa)+a*kappa+b)-integ(density(kappa))
    expected_shift=a*(.4+.3)+b
    checks.append(dict(name='affine_density_energy_shift',absolute_error=abs(actual_shift-expected_shift),
        passed=abs(actual_shift-expected_shift)<1e-12))
    checks.append(dict(name='reflection_signed_density',original=integ(np.ones_like(s)),
        reflected=integ(-np.ones_like(s)),passed=abs(integ(np.ones_like(s))-1)<1e-14))
    # Second and mixed parameter derivatives are compared against actual energy
    # differences, separately from any constrained-minimum interpretation.
    densitysecond=lambda q:3*q*q+1
    xiprime=2*s-3*s*s
    expected_second=integ(densitysecond(kappa)*etaprime**2)
    expected_mixed=integ(densitysecond(kappa)*etaprime*xiprime)
    base_energy=integ(density(kappa))
    for h in (1e-2,1e-3,1e-4):
        actual_second=(integ(density(kappa+h*etaprime))-2*base_energy+
            integ(density(kappa-h*etaprime)))/(h*h)
        actual_mixed=(integ(density(kappa+h*etaprime+h*xiprime))-
            integ(density(kappa+h*etaprime-h*xiprime))-
            integ(density(kappa-h*etaprime+h*xiprime))+
            integ(density(kappa-h*etaprime-h*xiprime)))/(4*h*h)
        errors=[abs(actual_second-expected_second),abs(actual_mixed-expected_mixed)]
        tol=max(3e-7,2*h*h)
        checks.append(dict(name='second_and_mixed_variations',step=h,
            expected=[expected_second,expected_mixed],absolute_errors=errors,
            tolerance=tol,passed=max(errors)<tol))
    signed=integ((1-2*s)**2)
    checks.append(dict(name='second_variation_sign_is_not_fixed',positive=signed,
        negative=-signed,passed=abs(signed-1/3)<1e-13))
    # Integrate the same density on separate domains without reusing the full
    # domain evaluation; all nodes are remapped independently.
    integrate=lambda fun,a,b:float((b-a)*np.dot(weights,fun(a+(b-a)*s)))
    theta_fun=lambda q:.2+.4*q+.3*q*q+.2*np.sin(np.pi*q)
    kappa_fun=lambda q:.4+.6*q+.2*np.pi*np.cos(np.pi*q)
    cuts=[0,.23,.71,1]
    parts=[integrate(lambda q:density(kappa_fun(q)),a,b) for a,b in zip(cuts,cuts[1:])]
    split_error=abs(sum(parts)-base_energy)
    checks.append(dict(name='energy_interval_additivity',parts=parts,
        absolute_error=split_error,passed=split_error<1e-12))
    alpha=.63
    before=np.array([integ(np.cos(theta)),integ(np.sin(theta))])
    after=np.array([integ(np.cos(theta+alpha)),integ(np.sin(theta+alpha))])
    rotation=np.array([[np.cos(alpha),-np.sin(alpha)],[np.sin(alpha),np.cos(alpha)]])
    rotation_error=float(np.max(np.abs(after-rotation@before)))
    checks.append(dict(name='curvature_reconstruction_rotation',angle_difference=alpha,
        absolute_error=rotation_error,passed=rotation_error<1e-12))
    # A nonconstant-curvature stationary curve for epsilon(q)=q^2/2:
    # theta=4 atan(exp(s-1/2)), theta''=sin(theta), lambda=-1, mu=0.
    # Solve the two nonlinear endpoint constraints by Newton iteration.  This
    # numerical construction is independent of the implicit-function proof.
    th=4*np.arctan(np.exp(s-.5)); kap=2/np.cosh(s-.5)
    w=s*(1-s); wp=1-2*s
    u=-w*np.sin(th); v=w*np.cos(th)
    up=-wp*np.sin(th)-w*np.cos(th)*kap
    vp=wp*np.cos(th)-w*np.sin(th)*kap
    gram=np.array([[-integ(np.sin(th)*u),-integ(np.sin(th)*v)],
                   [integ(np.cos(th)*u),integ(np.cos(th)*v)]])
    phi=w*(1+.3*s+.7*s*s)
    phip=wp*(1+.3*s+.7*s*s)+w*(.3+1.4*s)
    projection=np.linalg.solve(gram,[-integ(np.sin(th)*phi),integ(np.cos(th)*phi)])
    tangent=phi-projection[0]*u-projection[1]*v
    tangentprime=phip-projection[0]*up-projection[1]*vp
    target=np.array([integ(np.cos(th)),integ(np.sin(th))])
    def corrected(t):
        ab=np.zeros(2)
        for iteration in range(20):
            angle=th+t*tangent+ab[0]*u+ab[1]*v
            residual=np.array([integ(np.cos(angle)),integ(np.sin(angle))])-target
            if np.max(np.abs(residual))<2e-15:break
            jac=np.array([[-integ(np.sin(angle)*u),-integ(np.sin(angle)*v)],
                          [integ(np.cos(angle)*u),integ(np.cos(angle)*v)]])
            ab-=np.linalg.solve(jac,residual)
        else:raise RuntimeError('Endpoint correction did not converge')
        curved=kap+t*tangentprime+ab[0]*up+ab[1]*vp
        return integ(curved*curved/2),ab,float(np.max(np.abs(residual))),iteration
    naive=integ(tangentprime**2)
    constrained=integ(tangentprime**2+np.cos(th)*tangent**2)
    base=integ(kap*kap/2)
    first_constraints=[-integ(np.sin(th)*tangent),integ(np.cos(th)*tangent)]
    checks.append(dict(name='nonstraight_constraint_rank',eigenvalues=np.linalg.eigvalsh(gram).tolist(),
        tangent_constraint_errors=first_constraints,
        passed=np.min(np.linalg.eigvalsh(gram))>0 and max(map(abs,first_constraints))<1e-13))
    for h in (4e-2,2e-2,1e-2):
        plus,ap,rp,ip=corrected(h); minus,am,rm,im=corrected(-h)
        actual=(plus-2*base+minus)/(h*h)
        err=abs(actual-constrained); tol=max(5e-9,5e-5*h*h)
        checks.append(dict(name='exact_constraints_and_constrained_second_variation',step=h,
            corrections=[ap.tolist(),am.tolist()],constraint_residual=max(rp,rm),
            newton_iterations=[ip,im],expected=constrained,actual=actual,
            unconstrained_second_variation=naive,absolute_error=err,tolerance=tol,
            passed=max(rp,rm)<3e-14 and err<tol and abs(naive-constrained)>1e-7))
    # At a straight line the linearized kernel contains unrealizable directions.
    # eta=s(1-s)(s-1/2) has zero integral and negative quadratic Hessian -1/20.
    ep=-3*s*s+3*s-.5
    negative=-integ(ep*ep)
    checks.append(dict(name='straight_degeneracy_negative_hessian',second_variation=negative,
        expected=-1/20,passed=abs(negative+1/20)<1e-13))
    result=dict(timestamp_utc=datetime.now(timezone.utc).isoformat(),kind='numerical corroboration, not proof',
        numpy_version=np.__version__,quadrature='128 point Gauss-Legendre on [0,1]',checks=checks,
        passed=all(c['passed'] for c in checks))
    (ROOT/'verification'/'examples.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,ensure_ascii=False))
    return result['passed']

if __name__=='__main__':raise SystemExit(0 if run() else 1)
