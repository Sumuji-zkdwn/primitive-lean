"""Numerical corroboration of scaling, weights and conditional response examples.

Actual reparameterized integrals and finite differences are compared with the
derived formulas. This file does not establish general theorems or fit sensory
data. It only writes a result in this independent project.
"""
from pathlib import Path
from datetime import datetime, timezone
import json
import numpy as np

ROOT = Path(__file__).resolve().parents[1]


def run():
    nodes, weights = np.polynomial.legendre.leggauss(128)
    def integral(fun, left, right):
        points = left + (right-left)*(nodes+1)/2
        return float((right-left)/2*np.dot(weights, fun(points)))
    theta = lambda s: .2+.4*s+.3*s*s+.2*np.sin(np.pi*s)
    curvature = lambda s: .4+.6*s+.2*np.pi*np.cos(np.pi*s)
    density = lambda q: q**4/4+q*q/2+.3*q
    energy = integral(lambda s: density(curvature(s)), 0, 1)
    checks = []
    for scale in (.4, 2.3):
        # Differentiate the scaled angle numerically, rather than substituting
        # the derived curvature formula into both sides of the energy identity.
        h = 1e-5*scale
        scaled_curvature = lambda s: (theta((s+h)/scale)-theta((s-h)/scale))/(2*h)
        actual = integral(lambda s: density(scaled_curvature(s)), 0, scale)
        predicted = scale*integral(lambda s: density(curvature(s)/scale), 0, 1)
        position_errors = [abs(integral(lambda s: trig(theta(s/scale)), 0, scale)
                               -scale*integral(lambda s: trig(theta(s)), 0, 1))
                           for trig in (np.cos, np.sin)]
        error = abs(actual-predicted)
        checks.append(dict(name='similarity_general_density', scale=scale,
            finite_difference_step=h, actual_energy=actual, expected_energy=predicted,
            absolute_error=error, position_errors=position_errors, tolerance=2e-8,
            passed=error<2e-8 and max(position_errors)<1e-12))
    for degree in (2., 3.4):
        scale = 1.7
        original = integral(lambda s: abs(curvature(s))**degree, 0, 1)
        actual = integral(lambda s: abs(curvature(s/scale)/scale)**degree, 0, scale)
        predicted = scale**(1-degree)*original
        checks.append(dict(name='homogeneous_density_scaling', degree=degree,
            scale=scale, actual=actual, expected=predicted,
            passed=abs(actual-predicted)<1e-12))
    beta = .7
    cut = .37
    parts = [integral(lambda s: density(curvature(s)), a, b)
             for a, b in ((0,cut),(cut,1))]
    actual_weight = np.exp(-beta*energy)
    product_weight = np.prod(np.exp(-beta*np.array(parts)))
    checks.append(dict(name='weight_composition_and_inverse', parts=parts,
        weight=float(actual_weight), product=float(product_weight),
        inverse_energy=float(-np.log(actual_weight)/beta),
        passed=abs(actual_weight-product_weight)<1e-13
               and abs(-np.log(actual_weight)/beta-energy)<1e-13))
    eta_prime = lambda s: 1-1.6*s-.6*s*s
    derivative = integral(lambda s: (curvature(s)**3+curvature(s)+.3)*eta_prime(s),0,1)
    h = 1e-4
    energy_path = lambda t: integral(lambda s:density(curvature(s)+t*eta_prime(s)),0,1)
    measured = (np.exp(-beta*energy_path(h))-np.exp(-beta*energy_path(-h)))/(2*h)
    predicted = -beta*actual_weight*derivative
    checks.append(dict(name='actual_weight_first_variation',step=h,actual=float(measured),
        expected=float(predicted),absolute_error=float(abs(measured-predicted)),
        tolerance=2e-8,passed=abs(measured-predicted)<2e-8))
    # An exact feasible family of positive-curvature curves: the second half
    # of the tangent field cancels the first half, for every parameter t.
    length = 2*np.pi
    angle = lambda s,t: s+t*np.sin(2*s)
    kap = lambda s,t: 1+2*t*np.cos(2*s)
    quadratic_energy = lambda t: integral(lambda s:kap(s,t)**2/2,0,length)
    base = quadratic_energy(0)
    # Circle, lambda=mu=0, Q=int (2 cos 2s)^2 ds=4 pi.
    q = 4*np.pi
    for h in (.02,.01,.005):
        wp=np.exp(-beta*quadratic_energy(h)); wm=np.exp(-beta*quadratic_energy(-h))
        actual=(wp-2*np.exp(-beta*base)+wm)/(h*h)
        expected=-beta*np.exp(-beta*base)*q
        residuals=[abs(integral(lambda s:trig(angle(s,t)),0,length))
                   for trig in (np.cos,np.sin) for t in (-h,h)]
        error=abs(actual-expected); tolerance=4*h*h
        checks.append(dict(name='exact_family_weight_second_variation',step=h,
            actual=float(actual),expected=float(expected),absolute_error=float(error),
            tolerance=tolerance,endpoint_residual=max(residuals),
            passed=error<tolerance and max(residuals)<1e-12))
    def response(p,z):
        return np.log(z) if p==0 else np.expm1(p*np.log(z))/p
    def potential(p,K,k0,k):
        z=k/k0
        if p==0:return K*(k*np.log(z)-k+k0)
        if p==-1:return K*(k-k0-k0*np.log(z))
        return K*k0/p*(np.expm1((p+1)*np.log(z))/(p+1)-(z-1))
    K,k0 = 1.3,.8
    values=np.array([.25,.8,1.7,3.])
    for p in (-1.,0.,.55,1.,2.4):
        h=2e-4
        first=(potential(p,K,k0,values+h)-potential(p,K,k0,values-h))/(2*h)
        second=(potential(p,K,k0,values+h)-2*potential(p,K,k0,values)
                +potential(p,K,k0,values-h))/(h*h)
        predicted_first=K*response(p,values/k0)
        predicted_second=K/k0*(values/k0)**(p-1)
        errors=[float(np.max(abs(first-predicted_first))),
                float(np.max(abs(second-predicted_second)))]
        checks.append(dict(name='conditional_density_actual_derivatives',exponent=p,
            step=h,curvatures=values.tolist(),absolute_errors=errors,
            tolerance=2e-5,minimum_second_derivative=float(min(predicted_second)),
            passed=max(errors)<2e-5 and min(predicted_second)>0))
    for p in (-1e-5,1e-5):
        error=float(np.max(abs(response(p,values)-np.log(values))))
        checks.append(dict(name='normalized_power_log_limit',exponent=p,
            positive_inputs=values.tolist(),absolute_error=error,tolerance=1e-5,
            passed=error<1e-5))
    actual=integral(lambda s:potential(1,K,k0,curvature(s)),0,1)
    quad=integral(lambda s:K/(2*k0)*curvature(s)**2,0,1)
    boundary=-K*(theta(1)-theta(0))+K*k0/2
    checks.append(dict(name='linear_response_quadratic_density_boundary_shift',
        actual_shift=actual-quad,expected_shift=boundary,
        passed=abs(actual-quad-boundary)<1e-12))
    # The boundary conditions are identical, while transforming the density
    # selects the circle from curves tied by the original linear density.
    t=.25
    energy_linear=integral(lambda s:kap(s,t),0,length)
    density_exponential=integral(lambda s:np.exp(-kap(s,t)),0,length)
    circle_density_exponential=length/np.e
    residuals=[abs(integral(lambda s:trig(angle(s,t)),0,length))
               for trig in (np.cos,np.sin)]
    checks.append(dict(name='whole_functional_vs_density_counterexample',parameter=t,
        original_energy=energy_linear,original_circle_energy=length,
        transformed_density_energy=density_exponential,
        transformed_circle_density_energy=circle_density_exponential,
        endpoint_residual=max(residuals),
        passed=abs(energy_linear-length)<1e-12 and max(residuals)<1e-12
               and density_exponential>circle_density_exponential+.1))
    for check in checks:
        check['passed']=bool(check['passed'])
    result=dict(timestamp_utc=datetime.now(timezone.utc).isoformat(),
        kind='numerical corroboration, not general proof or sensory measurements',
        numpy_version=np.__version__,quadrature='128 point Gauss-Legendre, remapped per interval',
        checks=checks,passed=all(c['passed'] for c in checks))
    (ROOT/'verification'/'scale-response.json').write_text(
        json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(passed=result['passed'],checks=len(checks),
        failures=[c for c in checks if not c['passed']]),ensure_ascii=False))
    return result['passed']


if __name__=='__main__':raise SystemExit(0 if run() else 1)
