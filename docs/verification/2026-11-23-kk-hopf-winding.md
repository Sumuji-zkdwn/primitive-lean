# Hopf equator clutching: link to a genuine Mathlib winding-number theorem

2026-11-23 JST. Stacked Draft on PR #235; ancestor proofs and main unchanged.

## Verified predecessor
The continuous north/south overlap transition is already a kernel-proved
map t(u,v,w)=(u,-v)/sqrt(u²+v²) into UnitPhase (the real unit circle).
On the equator u²+v²=1,w=0 this equals (u,-v).

## New kernel proof target

1. Define the actual unit-equator inclusion into the full-overlap base.
2. Prove by existing phase uniqueness that the previously compiled t
   restricts exactly to complex conjugation (u,v) -> (u,-v).
3. Define circleParam θ=(cos θ,sin θ), and prove the *actual* transition
   sends circleParam θ to circleParam(-θ).
4. Identify the real pair circle parametrization with the existing
   Mathlib complex Circle.exp θ, and the period-one AddCircle model
   via AddCircle.toCircle. Prove the transition corresponds to angle
   negation under this canonical identification.
5. Use Mathlib.Topology.Covering.FundamentalGroupCircle theorem
   AddCircle.windingNumber_zsmulLoop (n=-1) to obtain actual integer
   windingNumber=-1 of the standard reverse parametrized loop.

This is not a new definition of winding number or a hard-coded integer.
The theorem's normalization comes from the genuine fundamental group
equivalence already available in Mathlib.

The precise output of this stage is the clutching loop's degree/winding
under the circle angular parametrization. To claim a *first Chern class*
identity for a globally defined smooth principal bundle, a subsequent
formal theorem must identify the transition with the corresponding
bundle's clutching construction and its classifying cohomology invariant.
That final Chern-class theorem is explicitly NOT claimed here.

## Verification
Dedicated pinned Lean --trust=0, full dependency-chain compile,
individual #print axioms audit (no sorry or custom axiom), and an independent
symbolic equator regression check. Do not claim success before Actions runs.

Keep Draft and no automatic merge. Main and ancestors remain unchanged.
