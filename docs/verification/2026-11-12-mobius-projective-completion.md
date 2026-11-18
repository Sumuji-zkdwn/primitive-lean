# Möbius transformations over the extended complex line (2026-11-12)

## Base and original work

- Base main revision: 28721702d21720c37805fb64924253f3e1ace11f.
- Existing WFS theorems are unchanged in
  `linear_input/lean_check/WFSMobiusFourier.inc` and
  `linear_input/lean_check/WFSProjectiveSampling.inc`.
- Pinned project environment: Lean v4.30.0-rc2,
  Mathlib revision 5450b53e5ddc75d46418fabb605edbf36bd0beb6.

The upstream group, inversion, triple mapping, functional uniqueness and
proportionality theorems are credited to Fubin Yan and Kenneth Shum,
"Formalizing Extended Complex Numbers, Möbius Transformations, and Cross Ratio
in Lean 4" (2026): https://arxiv.org/abs/2606.20358

Original source: https://github.com/fubinyan/ComplexVariables/blob/bfdb91564bb5aafe0c3e7ec73501e43598146b13/MAT3253/Chapter02/EComplex.lean
Our vendor copy: `lean/Research/EComplexThirdParty.lean`.
License: Apache-2.0, retained in `licenses/Mobius-Apache-2.0.txt`.
The original bytes were not edited; it is an attributed dependency.

## New results

`lean/Research/MobiusProjectiveCompletion.lean`:
- The observed WFS involution matrix [[-1,0],[2,1]] has determinant -1.
- Its action on EComplex=Option Complex is order two, including infinity.
- The finite pole -1/2 maps to infinity, and infinity maps back to -1/2.
- An arbitrary invertible complex 2×2 matrix scales alternating brackets
  by its determinant.
- Complex-totalized cross-ratio invariance on homogeneous coordinates.
- General three-point transport/uniqueness are bridged to upstream theorems.

`lean/Research/MobiusProjectiveStructure.lean`:
- Image of the Möbius group acting on EComplex in Equiv.Perm EComplex,
  a concrete model of effective PGL(2,C).
- Two matrices act identically iff their coefficients are proportional.
- The cross ratio is invariant under nonzero scalings of each homogeneous
  coordinate representative.
- Canonical lifts, normalization, nonzero preservation, and equality of
  normalized matrix action with the actual EComplex fractional-linear action.
- A deliberately totalized Complex-valued extended cross-ratio invariant.

`lean/Research/MobiusSphericalCrossRatio.lean`:
- A new, *EComplex-valued* projective cross ratio, preserving actual infinity
  at a zero denominator (unlike totalized Complex division).
- A pair of numerator/denominator homogeneous coordinates for each cross ratio.
- Independent-scaling covariance, determinant-squared covariance, and
  invariance for arbitrary complex Möbius transformations acting on the
  *extended complex line*, including infinity.
- A concrete pole-value example and the ordinary finite WFS formula away
  from the pole.

Thus the algebraic projective-action and cross-ratio aspects are proved.
We do not assert conformality, circle-line preservation, Lorentz-group
isomorphisms, analytic topology of the sphere, or full Wikipedia coverage.
No original WFS physical response law is derived from elastica energy.

## Verification

Dedicated workflow: `.github/workflows/mobius-projective-completion.yml`.
At the exact checked-out PR revision:
- independently check rational examples with
  `python -B -X utf8 tools/check_mobius_projective_completion.py`
- compile all four new-source stages at Lean `--trust=0`
- audit theorem axioms using `lean/Research/MobiusProjectiveAudit.lean`
- no `sorry`, `admit`, `native_decide` proof placeholders allowed.

Earlier successful exact-head workflow for the first two extensions:
https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/43151217163 .
At that run all 16 selected audited theorems depend only on
propext, Classical.choice, Quot.sound. A new exact-head success is
required for the additional spherical-cross-ratio module.

The original upstream source emits inherited deprecated-tactic/unused-variable
warnings under Lean 4.30.0-rc2; no new warnings were observed in the
previously verified Structure extension.

## Meaning of zero denominators

The result is NOT a new division operation making 1/0 legal in the real or
complex field. EComplex contains a genuinely new point `none`, denoting
infinity. The WFS matrix acts as a total bijection on that enlarged state
space. The two-cycle pole <-> infinity is an equality of projective states.
