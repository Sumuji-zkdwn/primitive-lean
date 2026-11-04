# F16 saddle, two-branch Cantor coding, and the F0 obstruction (2026-11-02)

## Provenance

- Base: verified F16 PR #23, commit 675f2c50cf19e33446eceee24c060eb1a3dc783d.
- Source: `linear_input/lean_check/F16SaddleCantor.inc`, registered *after* `F16UnexpectedBridges.inc`.
- Independent rational test: `tools/check_f16_saddle_cantor.py`.
- No changes to original F16 sign table, Chebyshev definitions, or F0 source proofs.

## Strict mathematical distinction

The existing `reflection_sample` proves that the concrete F16 block-5 signed action
is J(x,y)=(y,x), and `normalized_block_formula` identifies this generator with
the row-gauged 2x2 block of the actual F16 pencil. This does not supply a
physical time evolution.

**New model choice:** Define S=(5I+4J)/3.
Then S(x,y)=((5x+4y)/3,(4x+5y)/3), determinant one, with eigen-directions
(1,1) and (1,-1), eigenvalues 3 and 1/3. In coordinates
u=x+y, v=x-y, one has S(u,v)=(3u,v/3). The Lean file proves these
equalities without an assumption of hyperbolicity.

**Additional, genuinely independent model choice:** Keep only ternary digits
0 and 2, and for each selected digit a use
H_a(u,v)=(3u-a,(v+a)/3). The Lean file proves injective
finite symbolic word coding, cardinality 2^n and the exact affine
relation to the F16-derived S. It does not prove a Hausdorff dimension
formula, limit-set construction, or conjugacy to a full shift.

A separate mathematical argument, not yet Lean-formalized, is as follows.
Restrict the piecewise map H=H_0 on u in [0,1/3] and H=H_2
on u in [2/3,1], with v in [0,1]. For the standard middle-third
Cantor set C, the compact product C x C is invariant under H;
its dynamics is conjugate to a two-sided full shift of two symbols,
periodic saddle points are dense, and dim_H(C x C)=2 log(2)/log(3).
The branch selection and translation are not conclusions about F16
itself.

## Obstruction from F0

The existing `LinearInputF0.A_B_collapse` proves that when K is idempotent,
Split/Collect reconstruct and splitting is compatible with K,
`step K Split Collect = K`. The new direct corollary shows
such a step has no genuine 2-cycle. Any genuine two-cycle must therefore
violate at least one of idempotence, reconstruction, or compatibility.
Extra history is one possible modification, not a necessary consequence
of this theorem.

## Reproduce and scope

- `python -B -X utf8 tools/check_f16_saddle_cantor.py`
- `python -B -X utf8 tools/verify.py --proof-only`

The latter uses pinned Lean 4/mathlib, joint `--trust=0` and
all-declaration axiom audit when run through the PR workflow.
A successful Python test is not a substitute for Lean compilation.
No Kaggle performance claim, general Smale-Birkhoff theorem,
or claim that all saddle points are fractal is made.
