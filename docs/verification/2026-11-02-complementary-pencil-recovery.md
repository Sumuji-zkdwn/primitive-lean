# Complementary pencil recovery — 2026-11-02

## Verified result

**SUCCESS**: [GitHub Actions run 41420522608](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41420522608),
exact code commit `362dd5d286155abeb01c685aa17bbbe9172548f8`, completed
2026-11-02 09:32:49 UTC (18:32:49 JST).

| Check | Observed result |
|---|---|
| Independent general/examples Lean compile and axiom audit | 44 theorems / 61 declarations, exit 0, no warnings |
| Complete proof-only integration and axiom audit | 902 theorems / 1129 declarations, both stages passed, no errors or warnings |
| Separately counted additions including actual F16 | 59 theorems / 81 declarations |
| Original PR #23 source/configuration/workflow preservation | 90 files byte-identical to the pinned baseline |
| Exact F16 regression | All 16 basis vectors and eight null vectors passed; singular ranks 12/12, paired rank 16 |

Full machine-produced reports and logs are in
[artifact 13130002385](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41420522608/artifacts/13130002385).
The durable [CI summary](../../evidence/ci/2026-11-02-complementary-recovery/summary.json)
records the exact run, commit, source hashes, and decoded report summaries.
Artifact ZIP SHA256: `c00cdc7db507ed1facbe8ee3cf5c8db7ed9d57beccb553459361b96ca3aecad3`.

The verification record and evidence summary are documentation added after that
successful code run. The verified proof and checker sources remain unchanged.
The separate [Japanese comparison notes](complementary-observation-comparison-notes.md)
cover the observation-kernel comparison and counterexamples.

## Scope and preserved baseline

This additive change starts at PR #23 commit
`675f2c50cf19e33446eceee24c060eb1a3dc783d`, whose
[Actions run 41316728844](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41316728844)
passed 843 theorems / 1048 declarations. The original PR #23 branch, proofs,
and CI workflow are retained. The new work is on a separate stacked branch.

The original 90 tracked proof/configuration/checker/workflow files are checked
against their Git blob hashes in `tools/complementary_recovery_baseline.json`.
The only edits to existing files register the three added supplements and
their descriptive scopes in `tools/verify_main_result.py` and `tools/verify.py`.

Pinned dependencies remain Lean `v4.30.0-rc2` and mathlib
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`.

## 1. General constructive theorem

Let `K` be a field with `(2 : K) ≠ 0`, let `n` be a finite index type, and let
`B,C : Matrix n n K`. Define

\[
A(t)=B+tC,\qquad O(v)=(A(1)v,A(-1)v).
\]

For an explicitly supplied matrix `D` satisfying `D*B=I`, define

\[
R_D(y_+,y_-)=D\left(\frac{y_++y_-}{2}\right).
\]

The Lean theorem `decode_observe` proves `R_D(O(v))=v`. Consequently the paired
observation is injective. The square-matrix wrapper `inverseDecode_observe`
uses mathlib's actual matrix inverse `B⁻¹` and the hypothesis `IsUnit B`.
There is no assumption that `A(1)` or `A(-1)` is invertible or singular.

The decoder is a right inverse only for compatible observations:

\[
\operatorname{Compatible}(y)\iff\exists v,\ O(v)=y.
\]

`recoveryEquiv` is the explicit equivalence between the state space and the
subtype of compatible observation pairs. Its forward map is `O` and its inverse
is exactly `R_D`. `unique_state` gives the unique preimage. Under invertible `B`,
compatibility also has the concrete test

\[
C B^{-1}\left(\frac{y_++y_-}{2}\right)=\frac{y_+-y_-}{2}.
\]

The pointwise kernel theorem, without invertibility of `B`, is

\[
\ker(B+C)\cap\ker(B-C)=\ker B\cap\ker C.
\]

The nonzero-two assumption is explicit; characteristic two is not silently
included. Invertibility of `B` is sufficient, not necessary, for paired
injectivity.

### Prose-to-theorem map

All names in this table have namespace `LinearInputComplementaryPencilRecovery`.

| Claim | Declaration |
|---|---|
| Average isolates `Bv` | `probe_average` |
| Half difference isolates `Cv` | `probe_difference` |
| Supplied left inverse reconstructs every state | `decode_observe`, `decode_leftInverse` |
| Pair is injective | `observe_injective` |
| Compatible data are reconstructed, including each component | `observe_decode_of_compatible`, `positive_reconstruction`, `negative_reconstruction` |
| Explicit inverse onto the observation image | `recoveryEquiv`, `unique_state` |
| Exact common kernel, then its triviality with a left inverse | `joint_kernel_iff`, `joint_kernel_trivial` |
| Actual inverse matrix, under `IsUnit B` | `inverseDecode_observe`, `inverseDecode_leftInverse` |
| Concrete compatibility criterion | `compatible_iff_difference` |

Source: `linear_input/lean_check/ComplementaryPencilRecovery.inc`.

## 2. The actual F16 example

The new module uses the existing `LinearInputF16Determinant.realPencilAll t`,
whose entries are the original signed-basis left action `L_e3+t L_e10` on
`Fin 16 → ℝ`. It does not replace that matrix by a two-dimensional normal form.

`pencil_identification` proves entrywise that it is the general `pencil` with
`baseMatrix=realPencilAll 0` and `slopeMatrix` equal to the original `entryTen`.
`baseMatrix_isUnit` uses PR #23's `zero_probe_isUnit`; `baseMatrix_det` uses the
existing determinant theorem to obtain determinant one.

The actual decoder is

\[
R(y_+,y_-)=A(0)^{-1}\left(\frac{y_++y_-}{2}\right).
\]

`reconstruct_observations` applies the general inverse theorem to prove it
recovers every real 16-vector. On compatible data,
`plus_observation_reconstruct` and `minus_observation_reconstruct` prove
`A(1)R(y)=y_+` and `A(-1)R(y)=y_-`, respectively.

`singular_probes_exact_recovery` combines the unchanged rank-12 theorems for
both probes with the new constructive recovery. `joint_kernel_zero` proves
their common kernel is zero. Each kernel has dimension four by the existing
rank-12 result and rank-nullity; this explanatory dimension calculation is
not introduced as a new separately named Lean theorem here.

All new F16 names have namespace `LinearInputF16ConstructiveRecovery`.
Source: `linear_input/lean_check/F16ConstructiveRecovery.inc`.

## 3. Counterexamples and limits

These are formalized in `LinearInputComplementaryObservationExamples`.

| Case | Result and boundary | Lean declaration |
|---|---|---|
| Over ℝ, `B=C=0` | Distinct states have identical paired observations | `zero_pencil_collision` |
| A repeated nonzero projection `B(x,u)=(x,0)`, `C=0` | More observations do not help if the same nonzero kernel remains | `repeated_projection_collision` |
| Over ℝ, `B=0`, `C=1` | The pair `(x,-x)` is injective; `B` invertible is not necessary | `singular_center_can_be_injective`, `singular_center_alternative_decoder` |
| Over `ZMod 2`, `B=C=1` | `B` is invertible but both probes vanish; exclude characteristic two | `characteristic_two_collision` |
| Over ℝ, `B=1`, `C=0`, data `(1,0)` | Data are not realizable and decode/re-observe does not return them | `inconsistent_pair_not_realizable`, `inconsistent_pair_not_reconstructed` |

The scalar examples are one-dimensional linear pencils. They are stated as
direct scalar formulas rather than hidden changes to the generic theorem's
assumptions. The general theorem is exact and does not claim stability or a
noise bound for approximate data.

## 4. Limited comparison with PR #19

Source is PR #19 at exact head
`6bd74237f7b1910942988e6f542987857e9dec91`, specifically
[`WFSMobiusFourier.inc`](https://github.com/Sumuji-zkdwn/primitive-lean/blob/6bd74237f7b1910942988e6f542987857e9dec91/linear_input/lean_check/WFSMobiusFourier.inc).
Its `trace4_values`, `even_fourier_trace`, and `odd_fourier_trace` identify the
coordinate observations `(x,-u,-x,u)`.

The new Examples module independently checks this explicit coordinate form.
It does not import, merge, or recompile the separate PR #19 branch, and the
association with its `trace4` is source-based through the cited existing theorem.
No common dynamics or physical interpretation is asserted.

| Property | F16 | PR #19 four-phase coordinate form |
|---|---|---|
| State | `v ∈ ℝ^16` | `(x,u) ∈ ℝ²` |
| Two observations | `A(1)v`, `A(-1)v` | `E=(x,-x)`, `O=(-u,u)` |
| Individual kernel | Each dimension 4 | `ker E={x=0}`, `ker O={u=0}` |
| Intersection | `{0}` | `{0}` |
| Information retained jointly | All 16 coordinates | Both coordinates |
| Explicit decoder on the image | `A(0)⁻¹((y₊+y₋)/2)` | `(E.first,O.second)` |
| Compatible four-phase data | General pencil difference criterion | `q₂=-q₀` and `q₃=-q₁` |

There is a useful distinction: averaging the **raw** even/odd readouts gives

\[
\frac{E+O}{2}(x,u)=\left(\frac{x-u}{2},\frac{u-x}{2}\right),
\]

which is singular. `phase_average_collision` proves that `(0,0)` and `(1,1)`
produce the same average. Thus these raw observations share the zero-common-
kernel property with F16 but do not satisfy the same invertible-center premise.
Also, two 4-dimensional F16 kernels with trivial intersection span dimension 8,
not all 16 dimensions; they are not a direct-sum decomposition of the entire
state space. This stronger decomposition does hold for the two coordinate
axes in the 2-dimensional phase example and is not claimed as a common fact.

The coordinate results include `complementary_phase_kernels`,
`phase_pair_decode`, `phase_decode_trace`, `phase_trace_injective`, and
`phase_compatible_iff_realizable`.

## 5. Verification protocol and current status

Local exact rational checks passed for the original 16 F16 basis vectors,
eight explicit null vectors, both rank-12 probes, the paired rank 16,
re-observation of both components, generic examples of dimensions 1/2/3/5,
and the counterexample/phase-coordinate cases. This is independent finite
regression, not a substitute for Lean.

The new workflow preserves the old workflow and runs:

1. The existing exact-arithmetic tests and `tools/check_complementary_recovery.py`.
2. `tools/verify_complementary_recovery.py --standalone`: imports only mathlib
   and the generic/examples modules, compiles with `--trust=0`, and audits every
   public declaration. No F16 or Elastica theorem is used in this stage.
3. The unchanged orchestration command `python -B -X utf8 tools/verify.py --proof-only`,
   including the new modules in the existing combined proof/axiom audit.
4. `tools/verify_complementary_recovery.py --integration`: verifies matching
   source hashes and audits the additional declarations as separate groups.
5. Both new checks verify byte preservation of the 90 baseline files.

The allowed axiom set remains `propext`, `Classical.choice`, `Quot.sound`.
The checkers reject `sorry`, `admit`, newly declared axioms, `unsafe`,
`native_decide`, incomplete audits, unexpected axioms, and Lean warnings.

The completed CI observed 59 added theorems / 81 added declarations:
general 24/30, F16 15/20, examples 20/31. The integrated totals are
902 theorems / 1129 declarations. All counts, source hashes, successful stages,
and the original-source preservation result are recorded in the CI summary
linked above. The standalone check covers the general/examples modules; the
15 F16 theorems and 20 F16 declarations are verified in the complete integration
against the original matrix definitions and then reported as their own group.

The first two development runs failed on elaboration/linter and scoped-command
syntax issues, respectively. Those runs are not treated as successful evidence.
The successful run cited here follows the corresponding proof-script fixes;
the mathematical hypotheses and conclusions did not change.
