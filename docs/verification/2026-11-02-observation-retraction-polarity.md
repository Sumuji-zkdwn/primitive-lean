# Complementary recovery as an F0 retraction and a polarity closure

## Actual dependency bridge

`ObservationRetractionPolarity.inc` connects the exact decoder of PR #25 to
the F0 and fixed-set polarity statements of PR #26. It changes no original
proof, decoder, relation, or matrix. Register its sole namespace
`LinearInputObservationRetractionPolarity` after both
`ComplementaryPencilRecovery.inc` and `StrangeOperatorFixedSets.inc` in the
existing joint supplement checker.

For an encoder `E : α → β` and decoder `D : β → α` satisfying `D(E(x))=x`,
define the data-space map `P(y)=E(D(y))`. The new file proves:

| Claim | Declaration | Explicit hypothesis |
|---|---|---|
| `P` is an F0 idempotent | `retract_idempotent` | `Function.LeftInverse D E` |
| The decoded state is preserved by `P` | `decode_retract` | The same left-inverse condition |
| Fixed points are exactly realizable data | `retract_fixed_iff`, `fixedStates_retract` | The same condition |
| `P` fibers are exactly decoder fibers | `retract_fiber_iff` | The same condition |
| `Stops T P` means that some unrealizable datum becomes realizable under `T` | `stops_retract_iff` | The same condition |
| A nontrivial `P` stops itself | `retract_self_stops` | A datum outside `range E` |
| `Close Stops {P}` consists exactly of operators with fixed set `range E` | `close_retract_exact` | A state witness and a datum outside `range E` |
| An onto encoder instead gives universal singleton closure | `close_retract_of_surjective` | Surjectivity of `E` |

The matrix specialization uses the *existing* PR #25 definitions
`observe B C`, `decode D`, and the proved `decode_leftInverse`, where
`D * B = 1` and `2 ≠ 0` over a field. Its retraction is called `pairRetract`.
The wrappers prove idempotence, the exact compatibility criterion, the
meaning of `Stops`, and the exact singleton closure.

The properness condition is not left implicit: `pairRetract_opposite` proves
that `(w,-w)` is sent to `(0,0)`, and `opposite_compatible_iff` proves this
pair is compatible exactly when `w=0`. Thus
`close_pairRetract_exact_of_nonzero` supplies a concrete inconsistent-data
witness from any nonzero state vector. A zero-dimensional vector space does
not supply such a witness and belongs to the separate surjective case.

## Meaning and boundary

This F0 map acts on *pairs of observations*, whereas the original decoder
recovers the *state* exactly. Idempotent correction of inconsistent data is
therefore compatible with lossless recovery of all encoded states. It does
not assert that state dynamics are idempotent, nor that every arbitrary pair
is physically realizable.

The polarity closure preserves only the fixed-point set. Its members need
not be idempotent, linear, or equal to the decoder-induced map. The theorem
does not strengthen PR #26's boundary results. No statistical noise model,
optimal projection, physical conversion law, infinite fractal, or numerical
conditioning claim is added.

## Verification record

This additive module contains **16 theorems and 2 definitions**. On
2026-11-02 a fresh development assembly compiled with pinned Lean
`--trust=0`, exit code 0, no errors or warnings. Every one of the 18 new
declarations was axiom-audited; only the repository's allowed `propext`,
`Classical.choice`, and `Quot.sound` occurred. The checked module SHA-256 was
`bbb56f48f843396f249db79f47da41bb7ed2a41030852b37029c8ef3ed6b4d81`.

The development assembly combined the prior checked 733-theorem source with
the actual general complementary-recovery module and actual Stops,
conjugacy, and fixed-set modules, then appended this new module. It reused
the pinned dependency cache and did not perform a fresh project build.
This development check is distinct from the final integrated proof-only
run: these declarations must also be registered in that full run, whose
report records the final combined source hashes and outcome.

No proof placeholders, extra axioms, or native evaluation are introduced.
