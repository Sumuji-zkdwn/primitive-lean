# F16–Chebyshev–D4–two-probe bridge (2026-11-01)

## Provenance and scope

- Parent: PR #3 research branch `codex/primitive-history-derivation-20261029`.
- Source sign convention: the **unchanged** `F16Holonomy.inc` epsilon table from the user's `E_atlas_F16_smooth_v4_2026-10-22.zip`.
- Dependencies already present on parent: `F16RecoverySpectrum.inc`, `F16RealDeterminant.inc`, `F16CompleteRank.inc`, `VariablePairGaloisBridge.inc`.
- New source: `F16UnexpectedBridges.inc`.
- Theorem registration: `tools/verify_main_result.py` (joint Lean `--trust=0` and full declaration axiom audit). Independent finite check: `tools/check_f16_unexpected_bridges.py`.
- All previously registered proof sources are left unchanged; no change to `main`.

## Connection A: real local normal forms

Original F16 left pencil: `A(t) = L_e3 + t L_e10`. The existing proof exhibits eight signed 2×2 blocks
`B_a(t)=[[alpha_a,t beta_a],[t gamma_a,delta_a]]`.
All four constant signs are ±1. Multiplying on the **left** by
`diag(alpha_a,delta_a)` gives

`D_a B_a(t)=[[1,t p_a],[t q_a,1]] = I + t J_a`,
`p_a=alpha_a beta_a`, `q_a=delta_a gamma_a`.

The new finite proof `signed_product` verifies `p_a q_a=-1` exactly
for `a=0,1,2,3`, `p_a q_a=+1` exactly for `a=4,5,6,7`.
Thus `J_a^2=-I` for the former and `J_a^2=I` for the latter.
`normalized_block_formula` identifies this with the **actual** F16
block table, not an unrelated 2×2 toy matrix. The statement
`J_a^2=±I` is also an immediate algebraic consequence of `p_a q_a=±1`.

Block 1 realizes `J(x,y)=(-y,x)`; block 5 realizes `R(x,y)=(y,x)`.
After identifying their two abstract coordinate planes, the new theorems
verify `J^4=I`, `R^2=I`, `RJR=J^3`, a concrete D4 representation.
This **does not** show that these maps are automorphisms of the full
non-associative sedenion algebra or that D4 is a Galois group of F16.

The linear gauge `C(x,y)=(x-y,x+y)` obeys
`C(R(x,y))=(-C_1(x,y),C_2(x,y))`, the same diagonal reflection normal
form seen in the separate WFS projective-lift draft PR #21.

## Connection B: determinant and Chebyshev criticality

The existing full determinant is

`det A(t)=(1-t²)^4(1+t²)^4`.

The existing Chebyshev normalized cubic discriminant is

`Delta(t) = cubicDiscriminant 4 (-3) t =432(1-t²)`.

Therefore `det A(t)=((1+t²)Delta(t)/432)^4` and

`rank A(t)=12 iff Delta(t)=0 iff t∈{-1,1}`.

Additionally the quadratic resolvent `X²−2tX+1` has discriminant
`4(t²−1)=−Delta(t)/108`.

These are **parameter-level equalities**. A common critical polynomial
does not establish an equivalence between the F16 dynamics, stationarity
branches and the Kummer field extension.

## Connection C: complementary lossy observations

At `t=±1` each 16×16 F16 matrix has rank 12, but

`A(1)+A(-1)=2A(0)`, and `det A(0)=1`.

The new theorem `opposite_probe_joint_injective` states that the map

`v ↦ (A(1)v, A(-1)v)`

is injective on `R^16`. This follows without estimating a 32×16 matrix's
rank: take the sum of the two outputs, divide by two, and apply the
inverse of the nonsingular `A(0)`. In particular, **both single probes
are lossy, yet the pair recovers the full state**.

This complements, but does not equate, PR #14's F0 bit recovery or
PR #19's odd/even temporal Fourier observations.

## Projective WFS comparison (separately tested)

PR #19's physical positive-intensity model has
`z=(e^(2x)-1)/2 > -1/2` and sampled update
`M(z)=-z/(1+2z)`. In the projective gauge `w=z/(1+z)=tanh(x)`,
`w(M(z))=-w(z)`. This fact is checked by rational arithmetic here.
It has **not** been newly imported from PR #19 into the F16 Lean
assembly; the corresponding cross-branch theorem still requires a
dependency-compatible merge of the research drafts. Neither does
this equate the F16 parameter `t` with a physical intensity.

## Verification protocol and exact boundary

Run:

```bash
python -B -X utf8 tools/check_f16_unexpected_bridges.py
python -B -X utf8 tools/verify.py --proof-only
```

The PR workflow should execute both, with `--trust=0`, pinned
Lean/mathlib revisions and full all-declaration axiom audit.

**Status:** this record describes the proposed exact proof obligations,
not a successful Lean run. Add the exact commit SHA, successful CI run
ID and source hashes only after inspecting actual CI evidence.
No Kaggle ARC score improvement is claimed.
