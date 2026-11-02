"""Finite numerical corroboration of compositions of the proved results.

These checks concern boundary-corrected similarity of the p=1 density, and
the normalized power/log response of the whole exponential energy weight.
They are not general proofs, measurements of sensation, or tests establishing
local minimality. No replacement existence or universally quantified claim
is inferred from the numerical samples.
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

    def response(p, z):
        return np.log(z) if p == 0 else np.expm1(p*np.log(z))/p

    length = 1.2
    theta = lambda s: .2+.15*s+.25*s*s+.3*np.sin(2*np.pi*s)
    curvature = lambda s: .15+.5*s+.6*np.pi*np.cos(2*np.pi*s)
    sample_curvature = curvature(np.linspace(0, length, 2001))
    signed_range = [float(np.min(sample_curvature)), float(np.max(sample_curvature))]
    turning = float(theta(length)-theta(0))
    K, k0 = 1.3, .8
    # The p=1 potential has a polynomial extension to signed curvature.
    # This direct evaluation does not use logarithms of negative curvatures.
    p1_density = lambda k: K/(2*k0)*(k-k0)**2
    base_p1_energy = integral(lambda s: p1_density(curvature(s)), 0, length)
    checks = []

    for scale in (.4, 2.3):
        # Evaluate the scaled curve independently by differentiating its angle.
        h = 1e-6*scale
        scaled_curvature = lambda s: (theta((s+h)/scale)-theta((s-h)/scale))/(2*h)
        actual = integral(lambda s: p1_density(scaled_curvature(s)), 0, scale*length)
        turning_correction = K*(1/scale-1)*turning
        length_correction = K*k0/2*(scale-1/scale)*length
        expected = base_p1_energy/scale+turning_correction+length_correction
        error = abs(actual-expected)
        tolerance = 2e-7
        checks.append(dict(name='p1_similarity_with_boundary_correction', scale=scale,
            K=K, reference_curvature=k0, length=length, turning=turning,
            sampled_signed_curvature_range=signed_range, finite_difference_step=h,
            original_energy=base_p1_energy, actual_scaled_energy=actual,
            homogeneous_term=base_p1_energy/scale, turning_correction=turning_correction,
            length_correction=length_correction, expected_energy=expected,
            absolute_error=error, tolerance=tolerance,
            passed=error<tolerance and signed_range[0]<0<signed_range[1]))

    # The response below is applied to the whole energy weight. It is not
    # applied pointwise to the density before integration.
    density = lambda k: k*k/2+.1*k
    eta_prime = lambda s: length+(.4*length-2)*s-.6*s*s
    energy_path = lambda t: integral(
        lambda s: density(curvature(s)+t*eta_prime(s)), 0, length)
    energy = energy_path(0)
    first_energy_derivative = integral(
        lambda s: (curvature(s)+.1)*eta_prime(s), 0, length)
    beta = .4
    whole_weight = float(np.exp(-beta*energy))
    for p in (-1., 0., .55, 1., 2.4):
        steps = [1e-4, 5e-5]
        measured = [float((response(p, np.exp(-beta*energy_path(h)))
                          -response(p, np.exp(-beta*energy_path(-h))))/(2*h))
                    for h in steps]
        expected = float(-beta*np.exp(-p*beta*energy)*first_energy_derivative)
        errors = [abs(value-expected) for value in measured]
        tolerance = 3e-8
        checks.append(dict(name='whole_weight_response_actual_first_variation',
            exponent=p, beta=beta, whole_energy=energy, whole_weight=whole_weight,
            energy_first_derivative=first_energy_derivative, steps=steps,
            measured_derivatives=measured, expected_derivative=expected,
            absolute_errors=errors, tolerance=tolerance, passed=max(errors)<tolerance))

    expected_log_response = -beta*energy
    exponents = [-1e-3, -1e-4, -1e-5, 1e-3, 1e-4, 1e-5]
    responses = [float(response(p, whole_weight)) for p in exponents]
    errors = [abs(value-expected_log_response) for value in responses]
    exact_zero_error = abs(float(response(0, whole_weight))-expected_log_response)
    checks.append(dict(name='whole_weight_response_log_limit', beta=beta,
        whole_energy=energy, whole_weight=whole_weight, exponents=exponents,
        response_values=responses, expected_limit=expected_log_response,
        absolute_errors=errors, zero_exponent_error=exact_zero_error,
        last_error_tolerance=1e-5,
        passed=errors[2]<errors[1]<errors[0] and errors[5]<errors[4]<errors[3]
               and max(errors[2], errors[5])<1e-5 and exact_zero_error<1e-14))

    cut = .43
    parts = [integral(lambda s: density(curvature(s)), left, right)
             for left, right in ((0, cut), (cut, length))]
    part_weights = np.exp(-beta*np.array(parts))
    exponents = [-1., 0., .55, 1., 2.4]
    actual = [float(response(p, whole_weight)) for p in exponents]
    transported = []
    for p in exponents:
        left, right = response(p, part_weights)
        transported.append(float(left+right+p*left*right))
    errors = [abs(left-right) for left, right in zip(actual, transported)]
    checks.append(dict(name='split_energy_transported_to_whole_weight_response',
        cut=cut, energy_parts=parts, weight_parts=part_weights.tolist(),
        exponents=exponents, whole_response=actual, transported_response=transported,
        absolute_errors=errors, tolerance=2e-12, passed=max(errors)<2e-12))

    for check in checks:
        check['passed'] = bool(check['passed'])
    result = dict(timestamp_utc=datetime.now(timezone.utc).isoformat(),
        kind='finite numerical corroboration, not general proof, local-minimum verification, or sensory measurements',
        numpy_version=np.__version__,
        quadrature='128 point Gauss-Legendre, remapped per interval',
        checks=checks, passed=all(check['passed'] for check in checks))
    (ROOT/'verification'/'combinations.json').write_text(
        json.dumps(result, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(dict(passed=result['passed'], checks=len(checks),
        failures=[check for check in checks if not check['passed']]), ensure_ascii=False))
    return result['passed']


if __name__ == '__main__':
    raise SystemExit(0 if run() else 1)
