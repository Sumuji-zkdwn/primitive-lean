# Initial Elastica → observational quotient: conditional bridge and finite countermodel

**Base examined:** `67fdf6b74bbbcb20dc70e7bf98b90471e329aa91` (the main commit audited by PR #98). The dependency report itself lives in PR #98 (`docs/dependency/README.md` at `a08cb8696e699a0a43551c88e2bf6757ca65295b`).

## Three kinds of connection (do not conflate)

1. **Existing kernel-term edges:** PR #98 records no proof, statement, or definition path from `LinearInputOperatorRefinement.strict_refinement_splits_quotient` to its initial layer. The theorem is proved using `encode_eq_iff` and quotient constructors; this is an observation about the *original* accepted proof term, not a mathematical independence argument.
2. **Mathematical derivability:** A structurally identical conditional splitting theorem is reproved in `lean/Research/ElasticaObservationQuotient.lean` using only Lean's quotient construction, without importing any later operator module. The result is a theorem of basic type theory (with quotients). The initial elastica propositions are not required to prove this abstract implication. The assumptions `hOld` and `hExt` are **not** deduced for arbitrary elastica curves.
3. **Conceptual/interpretive bridge:** The finite model interprets three labels as the actual smooth tangent angles `θ₀(s)=0`, `θ₁(s)=1`, `θ₂(s)=s` and reads out their initial signed curvature `κ(0)` using `Elastica.curvature`. The transition vocabulary is an *additional* choice. No theorem in the initial library ensures that the `freshStep` lookup operation can be realized by an admissible variation, local replacement preserving endpoints, energy descent, or physical dynamics.

## Explicit state/operation/observation correspondence

| Abstract input | Concrete finite interpretation | Status |
| --- | --- | --- |
| `α` | `Fin 3`; label `i` represents the tangent angle `angle i` | Defined in the new Lean module |
| `ω` | `ℝ`, a curvature readout | Definition instantiation |
| `K : α → ω` | `fun i => Elastica.curvature (angle i) 0` | Derived from initial `Elastica.Geometry` definitions; `K(0)=K(1)=0`, `K(2)=1` are Lean-checked |
| `ι`, `old : ι → α → α` | `Unit`; old action is the identity | Additional stipulated operation, not derived from the calculus of variations |
| `κ`, `fresh : κ → α → α` | `Unit`; new action sends label `1` to `2` and fixes `0,2` | Additional stipulated state-dependent operation |
| `run`, `ObsEq` | Arbitrary finite action words and equality of every resulting readout | New generic definitions |
| `State`, `forget` | Quotient by `ObsEq`, and canonical forgetting of the new action alphabet | Constructed from quotient logic |

The old partition is `{0,1} | {2}`; after adjoining `freshStep` the partition becomes `{0} | {1} | {2}`. The old quotient receives a surjection from the new quotient, and this surjection is not injective.

The countermodel uses the **same** three tangent angles, the **same** curvature readout, and the **same** old identity action, but adjoins `inertStep` (another identity) instead. It leaves the two partitions identical and makes the forgetful quotient map injective. Thus, the initial geometric definitions alone do not imply that *every* added action creates a new observational distinction.

## Exact proof boundary

The original theorem is an implication of the form

`ObsEq K old x y → ¬ObsEq K (sumStep old fresh) x y → ∃ q r, q ≠ r ∧ forget q = forget r`.

The first premise is observational indistinguishability and the second is actual strict refinement. General quotient logic derives the result *assuming both*. To derive an elastica-specific existence theorem, one needs an additional **realizability bridge** specifying a class of admissible curve transformations and proving that some admissible fresh operation breaks `ObsEq` without violating the original boundary, smoothness and/or energy constraints. The initial `Composition` and `ReplacementConsequences` theorems compare already-admissible smooth curves; they do not construct all state-dependent action transitions required here.

Consequently, the finite positive witness is a mathematically correct *curvature-labelled transition system*, not a demonstrated physical elastica replacement. The negative witness rules out an unconditional refinement claim; it does not disprove the conditional theorem and does not establish that no admissible refinement can ever occur.

## Verification

Run in repo root:

```sh
python -m unittest tests.test_elastica_observation_bridge -v
```

Run with the pinned Lean `v4.30.0-rc2` and Mathlib revision in `lean/lakefile.toml`:

```sh
cd lean
lake exe cache get
lake env lean --trust=0 Research/ElasticaObservationQuotient.lean
```

The Lean module prints the axioms of `strict_refinement_splits_quotient`, `K_two`, `curve_split`, and `inert_no_split`. The proposed stand-alone GitHub Actions workflow records the exact checkout SHA and runs these two checks. A CI result must be tied to the exact commit actually tested; a local Python pass does **not** substitute for a Lean kernel check.