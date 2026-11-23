# Continuous Hopf overlap transition: circle-valued map

Date: 2026-11-23 (JST). Stacked Draft PR on #233, itself stacked on
topological north and south chart homeomorphism PRs #230/#231.

## Goal

Define B_NS={b in S² : 1+b_z>0 and 1-b_z>0}.
Let D_N=sqrt(2(1+b_z)), D_S=sqrt(2(1-b_z)). The source-defined
transition function is

  t(b)=(2b_x/(D_N D_S), -2b_y/(D_N D_S)) in U(1).

The preceding KKHopfTransitionAlgebra.full_overlap_transition
has certified both t(b)∈U(1) and
rotate(t(b),northVec(b))=southVec(b) in the Lean kernel.

KKHopfTransitionContinuous now aims to construct the actual
subtype-valued map transition : OverlapBase → UnitPhase
and prove Continuous transition using positivity of both roots,
composition of continuous functions, division by nowhere-vanishing
functions, and continuity into the subtype circle.

The map is a genuine continuous gluing/transition candidate for a
topological principal circle bundle; this does NOT automatically
construct a smooth bundle atlas or complete a first Chern computation.

## Proof boundary

Success requires the new dedicated CI to pass pinned Lean --trust=0
compilation, axiom audit, existing full-overlap SymPy oracle, and source
SHA audit. Before that the source is an unverified Lean proof candidate.

The explicit degree -1 of the restricted equatorial conjugation map is
a classical consequence, but Mathlib winding number/degree and the
identification with the clutching map have NOT yet been connected in
the kernel. Do not present a Chern theorem as completed.

Keep DRAFT; no merges or changes to ancestor PRs or main.
