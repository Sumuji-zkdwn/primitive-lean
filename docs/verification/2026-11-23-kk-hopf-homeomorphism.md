# Attempted topological Hopf quotient equivalence

Date 2026-11-23. This is an independent stacked Draft PR based on #226, whose prior CI has established (a) Hopf S³→S² surjectivity, (b) set-theoretic quotient equivalence with the true diagonal U(1) orbit relation, and (c) explicit north/south pointwise sections and phase uniqueness.

This PR attempts the next known topological result:

  (S³ / U(1), quotient topology) ≅ₜ S².

The proof strategy is to give the set-theoretic orbit quotient the coinduced topology used by Mathlib's Quotient type. Then prove:

1. S³ is compact, by viewing it as the closed polynomial level-set |X|²=1 inside the finite product compact cube [-1,1]^4.
2. The Hopf map is continuous, because all three coordinates are polynomials in four real coordinates.
3. The induced function from the quotient to the Hausdorff sphere S² is continuous by the quotient topology.
4. The prior kernel-checked equivalence upgrades to a homeomorphism by Mathlib's compact-to-T2 continuous-equivalence theorem.

This is a new Lean proof candidate until its actual dedicated pinned trust-zero CI completes. No analytic trigonometric inverse is assumed and the quotient topology is not defined ad hoc on the base.

**Scope:** A homeomorphism of orbit quotient and S² is not a smooth diffeomorphism, a Lean principal-bundle local trivialization, a proof that the Hopf transition has Chern number ±1, or a metric reduction/EMD curvature theorem. The base still uses the concrete polynomial unit sphere rather than Mathlib's abstract sphere bundles.

Keep Draft, no merge. Existing PRs #199, #215, #219, #222, #225, #226 and main untouched.

## Verified exact-head results

The dedicated [run 45118018154](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/45118018154) succeeded after making the continuity of each subtype coordinate explicit. The public Mathlib construction KKHopfHomeo.quotientHomeomorph is an actual Homeomorph between the quotient type, with Mathlib's quotient topology, and the concrete unit S² subtype.

The extended [run 45118462975](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/45118462975) also succeeded, covering KKHopfEquator.equator_transition and equator_transition_unique. These prove that on the base equator u²+v²=1 the north/south section transition is the **unique** unit phase (u,-v), i.e. complex conjugation, and its four real components are independently verified using exact SymPy.

Five named declarations (two continuity theorems, the homeomorphism definition and two equator theorems) passed individual Lean axiom auditing, with only propext, Classical.choice and Quot.sound dependencies. The compiled private compactness lemmas are transitively included through the homeomorphism's axiom dependency audit.

**Remaining limitations:** not yet a smooth quotient diffeomorphism, an explicit Mathlib principal-bundle trivialization, a formal winding number/first-Chern computation, or the general GH and EMD curvature theorems. The homeomorphism uses the quotient relation already proved equal to the circle orbit relation in parent PR #226. The explicit equator transition is a strong starting point, but degree -1 is still an external classical topological conclusion rather than a Lean result.
