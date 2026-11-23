# Finite metric-compatible Ricci trace covariance — algebraic bridge to smooth Yang–Mills

Date: 2026-11-22 (JST).
Dependency: draft PR #191 (which depends on #190, #189, #188, #187, #186).
Upstream mathlib: pinned by the parent repository, no change.
Status: DRAFT; only exact-head CI establishes kernel compilation.

## Why this is needed

PR #191 proves the *uncontracted* differential second Bianchi identity,
the contracted Bianchi identity, skew symmetry, and Riemann pair-exchange
for a smooth Mathlib Levi-Civita connection in an actual real-valued
frame. Its final Yang–Mills theorem still requires that the Ricci trace
of the covariant curvature derivative vanish.

The missing mathematical ingredient is **covariant derivative
commutes with a metric-compatible trace**:

    trace_g(nabla_e R) = nabla_e(trace_g R).

This PR formalizes the complete finite moving-frame calculation
rather than inserting "parallel Ricci" as an axiom or using the old
rational component proof. The trace is real-valued.

## Exact frame algebra

Fix a finite orthonormal frame indexed by Fin n. A real rank-four
curvature-component field is R(p,a,b,c,d), with a linear directional
scalar derivative ordinaryDeriv(e) on a chosen vector space of fields.
A moving metric-compatible orthonormal frame has skew connection
coefficients Gamma(p,e,i,j) = -Gamma(p,e,j,i).

The covariant derivative of a (0,4) tensor is built, not assumed:

    D_e R_abcd = partial_e R_abcd
               - sum_j Gamma_eaj R_jbcd
               - sum_j Gamma_ebj R_ajcd
               - sum_j Gamma_ecj R_abjd
               - sum_j Gamma_edj R_abcj.

The Ricci field is the contraction Ric_bd(p) = sum_i R(p,i,b,i,d).
Define its covariant derivative by differentiating this field and
subtracting the two connection corrections.

The core theorem proves:

    sum_i D_e R_ib i d = nabla_e Ric_bd,

including all four connection terms. The two terms from the repeated
index i cancel because Gamma_eij is skew and their curvature pairing
is symmetric under swapping i and j. This is proved via exact double
finite-sum reindexing in skew_double_sum_swap and
contracted_gamma_cancels; there is no assumption of the desired
trace equality.

Now **global Ricci=0** implies ordinaryDeriv(Ric)=0 by linearity, and
the two remaining covariant corrections also vanish. Thus the
contracted covariant derivative of curvature is zero with no
"parallel Ricci" assumption. Combining with the real second Bianchi
and pair-exchange already proved in the previous PRs yields the
source-free Yang–Mills curvature-divergence equation in this
metric-compatible finite frame model.

## The exact remaining analytic bridge

This is NOT an unconditional smooth Levi-Civita theorem yet.
The structure FrameJet packages a linear operator ordinaryDeriv
on scalar fields, a skew moving-frame Gamma, and real tensor fields.
It does **not automatically instantiate** the actual Mathlib
Levi-Civita connection or the local orthonormal frame. In particular:

1. Need a local C3 orthonormal frame around each x in the manifold,
   with its skew connection coefficients from the true smooth
   Levi-Civita connection.
2. Need a compatible interpretation of ordinaryDeriv on smooth scalar
   fields as the actual directional manifold derivative. Mathlib's
   mvfderiv on *all* functions is junk-valued on nonsmooth inputs,
   hence not directly a linear map on the whole function space.
3. Need to instantiate the four-slot correction formula for the
   actual smooth covariant curvature derivative, using the proven
   inner_covCurvature_expand_bridge of PR #191.
4. Need to identify the Ricci contraction in that frame with the
   actual geometric Ricci tensor and to translate global geometric
   Ricci=0 to vanishing of its frame components.

External prior formalization:
korbonits/ricci-flow-blueprint, Divergence.lean
  - sum_inner_covCurvature_eq: the complete smooth frame-covariant trace identity;
  - divCurvature_eq_covRicci_sub: the contracted second Bianchi.
These are implemented with real smooth connections and
IsOrthonormalFrameOn; porting them requires several large upstream
modules. The present PR isolates the finite trace identity and
cancellation required by a faithful port. It neither imports that
whole upstream Ricci-flow project nor misrepresents its theorems
as newly discovered results.

Reference: https://github.com/korbonits/ricci-flow-blueprint/blob/c8017e2c26898d11f39cec0dfce89368d5a0506a/RicciFlowBlueprint/Divergence.lean

## Checks

- Lean: lean/Research/RicciTraceCovariance.lean, pinned --trust=0.
- Independent Python: tools/check_ricci_trace_covariance.py, exact
  rational tests of random nonzero R and skew Gamma at multiple
  points, plus nonzero Ricci-flat algebraic Weyl-type curvature.
- Dedicated CI with axioms audit and exact-head source hashes.
- Status remains draft, with no main auto-merge.

The mathematical identity is known and serves the gravity-only
formalization program. This is not the derivation of independent
physical Yang–Mills bosons, SU(2) weak forces or quantum matter.
