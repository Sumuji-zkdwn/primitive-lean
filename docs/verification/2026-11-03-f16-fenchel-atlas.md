# 2026-11-03: F16 quadratic Fenchel slice and E atlas

This is a new additive source. It does not overwrite the source sign table,
the original polynomial E, the 16x16 pencil, or the prior verified results.

## Typed scope

The smooth F16 notes give the selected 2D restriction
V_t(s,v)=(1-t)^2 s^2+(1+t^2) v^2/2. In the original E family,
this is E(k=2(1-t)^2, lambda=0, a=1+t^2, c=0, x=s, y=v, u=0).

The new source reuses the actual E gradient Jacobian theorem to calculate
the Hessian determinant 2(1-t)^2(1+t^2), zero iff t=1.

Define the physical-pairing Fenchel score
B_t(p,q;s,v)=ps+qv-V_t(s,v), taking a supremum over all (s,v) in R^2.

- At t=0 it is maximized at (s,v)=(p/2,q), with value p^2/4+q^2/2.
- At t=1 it is bounded above exactly when p=0. Its maximum then is q^2/4.
  For p!=0, a constructive unbounded sequence follows from taking
  s=(B+1-q^2/4)/p, v=q/2 for any proposed bound B.
- At t=-1 this selected section is regular, and the maximum is
  p^2/16+q^2/4, attained at (p/8,q/2).

The older full-matrix theorem gives rank(L_t)=12 at both t=+1 and t=-1,
and rank=16 elsewhere. These are two different assertions. The 2D
section sees only the t=+1 null direction. It must not be used
to claim the full 16D Fenchel domain at t=-1.

## Reproduction

- Lean: linear_input/lean_check/F16FenchelAtlas.inc
- Exact regression: python -B -X utf8 tools/check_f16_fenchel_atlas.py
- Full Lean: python -B -X utf8 tools/verify.py --proof-only
- Integrated: python -B -X utf8 tools/verify.py --integration-only

## Not yet established in Lean by this supplement

1. Identity between this quadratic slice and the actual 16D matrix
   V_t(z)=1/2||L_t z||^2 on a declared 2-plane.
2. Full 16-dimensional Fenchel formula with pseudoinverse and effective
   domain range(L_t^T).
3. All 21 E variable pairs, all 42 projections and all 128 role choices
   as a duality-preserving classification.
4. A canonical F16-to-SO(2) geometric connection, rather than the
   explicit chosen embedding of signs into rotations.

No new claims on physical dynamics or the Jacobian conjecture.
