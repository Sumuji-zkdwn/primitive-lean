# Conditional 3D PAD identifiability -- finite formal bridge (2026-11-07)

**Status:** independent student research draft, NOT a validated liquid-jet physical model.
**Base:** `main` 67fdf6b74bbbcb20dc70e7bf98b90471e329aa91.
**Formal source:** `lean/PADFourLayer.lean` (10 theorems).
**Exact independent test:** `tools/check_pad_four_layer.py`.

## Why the earlier draft was rebuilt

Dupuy et al. (Phys. Rev. Lett. **130**, 156901, 2023) use an effective
one-dimensional Gaussian angular convolution for interpreting liquid PAD
anisotropy. Its exact algebraic fractional coordinate q(beta)=beta/(4+beta)
is **not** an exact coordinate of general three-dimensional transport.
The old coordinate and its 24.2% first-order comparison are withdrawn as
primary contributions to the revised paper.

## Conditional forward reduction

For normalized rotationally symmetric elastic scattering on the sphere,
the degree-2 spherical-harmonic eigenvalue c2(E) multiplies the anisotropy
coefficient once per independent collision, conditional on angular
acceptance and escape effects being neglected or separately modeled.

**Additional physical assumption:** if N|z,E is Poisson with mean
lambda_E*z, the average angular attenuation equals

    E[c2(E)^N | z,E] = exp(-lambda_E*z*(1-c2(E))).

**Another strong assumption:** a common *detected* depth distribution
across measured energies. Energy-dependent attenuation commonly violates
this and would require additional transport modeling.

For known, equally spaced four layers, the idealized normalized
observation becomes F_p(s)=p0+p1*s+p2*s^2+p3*s^3.
The rational parameter s should not be identified with a measured eKE
until an experimental energy-to-s calibration is supplied.

## Exact finite witnesses

Both probability vectors

    p+ = (11/60, 7/15,  1/60, 1/3)
    p- = (19/60, 1/30, 29/60, 1/6)

have mass 1 and mean 3/2. At t=4/5,
F_{p+}(t)=F_{p-}(t)=369/500. Yet

    F_{p+}(s)-F_{p-}(s) = (s-1)^2 * (s-4/5) / 6.

In particular, F_{p-}(1/2)-F_{p+}(1/2)=1/80.

If the mass and mean of a four-level profile are known independently,
two noiseless observations at distinct t,s not equal to 1 determine
the profile. The observation matrix has

    det M(t,s) = (s-t)*(1-t)^2*(1-s)^2.

The Lean file proves the equivalent coefficient-vanishing theorem over
rational weights. The determinant identity is checked independently by
exact arithmetic; no matrix-conditioning theorem is asserted in Lean.

### A necessary caveat: mean unknown

The distinct profiles

    u = (23/100, 67/200, 27/200, 3/10)
    v = (27/100, 33/200, 73/200, 1/5)

have identical mass and BOTH responses at 4/5 and 1/2, but means
301/200 and 299/200. They are checked in the separate paper's symbolic
audit. A known mean is not a free experimental assumption.

At (t,s)=(4/5,1/2) the observation matrix has determinant -3/1000,
and numerical 2-norm condition number about 1586. Exact identifiability
does not imply stability under measurement errors.

## The bridge into primitive-lean

- `OperatorWordObservations.inc`, theorem `pair_observation`:
  adding an observation refines indistinguishability.
- `OperatorWordObservations.inc`, theorem `postprocess`:
  processing an unchanged scalar readout cannot create distinctions.
- `ComplementaryPencilRecovery.inc`, theorem `joint_kernel_iff`:
  joint recovery is a common-kernel question.
- `PADFourLayer.lean`: an explicit *finite-dimensional* continuous-weight
  realization that states exactly when one and two probes separate states.

The generic existing files are proof precedents, not an imported Lean
dependency of this standalone sidecar. The finite-state horizon theorem
does NOT apply to rational-valued weights.

## Scientific limits and next experiments

This draft does NOT fit or reproduce the original measured PAD, recover
a real depth distribution, account for the full cylindrical liquid-jet
geometry, validate any particular Gaussian DCS, or establish scientific
novelty over earlier inverse-problem work. Schild et al. (J. Phys. Chem.
Lett. **11**, 1128-1134, 2020) already combined ab initio electron-water
cross sections with a Monte Carlo transport model.

To make it useful to Stephan Thurmer's laboratory, calibrate
c2(E), energy-dependent attenuation/selection and beta0(E), propagate
correlated errors, then choose additional actually accessible eKE values
by a **noise-aware separation criterion**, and validate on held-out data.

References:
- Dupuy et al. (2023), DOI: 10.1103/PhysRevLett.130.156901
- Schild et al. (2020), DOI: 10.1021/acs.jpclett.9b02910
- Thurmer et al. (2013), DOI: 10.1103/PhysRevLett.111.173005
- Dupuy et al. (2023), DOI: 10.1021/acs.accounts.2c00678
