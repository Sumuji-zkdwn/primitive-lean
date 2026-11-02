# F0 dynamics descent, Rule 481, and Hanna correction — formalization scope

Date: 2026-10-31. This is an additive supplement based on the PR #3 head,
which already contains F0Retractions, F0Counting, F0MergeChains,
BranchFibers, and GaloisChebyshev. Old proof bodies are unchanged.

## New Lean declarations and logical dependencies

1. **F0UpdateDescent.inc** (LinearInputF0Descent):
   * \`RespectsFibers K U := ∀ x y, K x = K y → K (U x) = K (U y)\`.
   * \`Descends K U := ∀ x, K (U (K x)) = K (U x)\`.
   * Under **explicit** \`LinearInputF0.Idempotent K\`,
     \`descends_iff_respects\` proves these two conditions equivalent.
   * \`induced\` constructs a map on \`LinearInputF0.Fixed K\`;
     \`induced_naturality\` proves it represents the original observable update
     when \`Descends\` holds. \`induced_unique\` proves uniqueness.
   * \`respects_comp\`, \`descends_comp\`, \`induced_comp\` formalize
     closure/composition.
   * \`equivariant_preserves_fixed\` shows any equivariant update preserves
     a previously symmetric state.
   * \`example_does_not_descend\` supplies a concrete three-state obstruction
     using the existing \`LinearInputF0.exampleK\` (not an axiom).

2. **Rule481Symmetry.inc** (LinearInputRule481):
   * The local five-bit rule is exactly Boolean center + twice the four
     Boolean neighbors; output 1 for scores 0,5,6,7,8.
   * \`reflect_ew\`, \`reflect_ns\`, \`complement\` prove the local invariances.
   * \`Grid := ZMod 3 → ZMod 3 → Bool\` is a **periodic 3x3 torus**.
   * \`step_mirror\` proves a full synchronous update commutes with
     north/south reflection; \`step_preserves_mirror\` reuses the general
     \`F0UpdateDescent.equivariant_preserves_fixed\` theorem.
   * Uniform zero and one grids form a 2-cycle; \`step_not_idempotent\`
     proves this update is NOT an F0-style idempotent forgetting map.
   * The 3x3 torus is **not** the infinite growing planar experiment defining
     OEIS A272457. It cannot establish the 34634 cumulative count.

3. **HannaJetCorrection.inc** (LinearInputHannaJets):
   * First jets over integer coefficients represent power series modulo x².
   * For the k=3 term in the alternative A322725 generating equation,
     the x^7 contribution without the denominator is 18 and the complete
     contribution is 26. Difference = 8.
   * This is an exact local certificate of the 6022→6030 discrepancy.
   * It does NOT prove the entire recursive series has coefficient 6022,
     nor the canonical series has 6030: those remain independent integer
     checks until the full fixed-point series is Lean-formalized.

## Computation, not proof

\`tools/check_f0_dynamics.py\` independently computes:
* labelled idempotents for n=1…8 (6322 at n=7);
* the exact canonical Hanna series through x^8 (6030 at x^7);
* the alternative fixed-point series with k=3 denominator omitted
  (6022 at x^7);
* Rule 481 on a sufficiently large periodic background, counting
  light-cone crops for stages 0…35 (cumulative 34634 at stage 35).

The \`python\` results do not establish mathematical derivability between
F0, the Hanna series, Rule 481, or optimal square packings.

## Verification route

The supplemental proof files are registered in \`tools/verify_main_result.py\`,
with honest scope entries in \`tools/verify.py\`. The CI workflow runs both
the integer smoke checks and the repository's existing check:

    python -B -X utf8 tools/check_f0_dynamics.py
    python -B -X utf8 tools/verify.py --proof-only

The latter compiles the assembled Lean source with \`--trust=0\` and audits
all public declarations for forbidden proof tokens and unapproved axioms.
Success is asserted only if a GitHub Actions job for this exact commit
has succeeded; a draft PR or a passing Python check is not proof verification.

## Still unproved / not claimed

* A combinatorial bijection from F0 histories to the Hanna coefficients.
* A general F0 construction deriving Rule 481 or A322725 from no new definitions.
* The count 34634 as a Lean theorem for the growing planar automaton.
* The exact 6022 coefficient of the full altered formal power series as a
  Lean theorem (as opposed to a first-jet correction and Python computation).
* The 11 cube nets, their folding history, or the optimal n=5 square packing
  within Lean, or a proof of any alien-sort packing optimum.
