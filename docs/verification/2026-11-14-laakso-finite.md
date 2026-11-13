# Finite Laakso observation extension — verification record, 2026-11-14

This extension formalizes a finite graph construction, an obstruction to
forgetting state by endpoint averaging, and an exact synchronized subsystem.
It also supplies an abstract set-level inverse-tower bridge to the existing
future-observation machinery. The three new modules contain **59 theorems and
114 declarations** in total. These are extension counts, not repository-wide
counts.

The machine-readable companion is
[2026-11-14-laakso-finite-results.json](2026-11-14-laakso-finite-results.json).
The unified local integration run **passed all 27 stages**. The combined
Lean compilation checked **4,732 theorems and 6,308 declarations** with
`--trust=0`, zero warnings, and no unexpected axioms. All 417 recorded
proof-input hashes were rechecked after completion. The main combined
compilation took 431.383 seconds; the sum of integration stage times was
714.376 seconds. This is a local working-tree result, with its source-hash
and cache conditions recorded below.

| Module | Formalized scope |
|---|---|
| [InverseTowerObservation.inc](../../linear_input/lean_check/InverseTowerObservation.inc) | Compatible sequences of a set-level inverse tower; coordinatewise deterministic and multi-action updates under explicit commuting-square hypotheses; projection and future-observation bridges; a nonempty binary-prefix example. |
| [LaaksoFiniteGraph.inc](../../linear_input/lean_check/LaaksoFiniteGraph.inc) | Binary trisect-and-glue refinement of labelled finite multigraphs; the raw quotient; distinct parallel-edge identities; and an explicit six-vertex, six-edge first approximant tied to the refinement construction. |
| [LaaksoNonlinearObstruction.inc](../../linear_input/lean_check/LaaksoNonlinearObstruction.inc) | Incidence-sum Laplacian on that first approximant, a chosen cubic reaction, failure of pair-mean descent for every real coupling coefficient, and a synchronized mass-weighted subsystem whose vector field and explicit Euler updates intertwine. |

The finite graph module concerns combinatorial vertices and labelled edges.
It does not construct the geometric realization by intervals, a metric or
measure inverse limit, Hausdorff dimension, or a Poincare inequality. The tower
module does not turn arbitrary finite graph data into a Laakso space.

For the nonlinear module, the chosen field is
`F_lambda(x) = 3*x - 4*x^3 - lambda*L*x`, with the cubic taken componentwise.
The two left endpoint values and the two right endpoint values are averaged
by `pairMean`; the internal wormhole values are forgotten. The uniform state
with every coordinate `1/2`, and the state with left values `3/4, 1/4` and all
other values `1/2`, have the same current mean `(1/2, 1/2)`. Their projected
fields are respectively `(1, 1)` and `(5/8, 1)`, for every real `lambda`.
Consequently, no deterministic vector field on the two endpoint means can
represent this field on all fine states.

The synchronized injection is `J(L,R,W1,W2) = (L,L,R,R,W1,W2)`. Its quotient
vertex masses are `(2,2,1,1)` and each of its three edge conductances is `2`.
The formalization identifies these weights with the actual vertex and edge
fiber multiplicities and proves endpoint compatibility. It then proves
`F_fine(J(q)) = J(F_sync(q))`, the corresponding identity for explicit Euler
updates, and the identity for every finite number of such updates using the
existing `representation_iterate` theorem. It also connects the obstruction
to `FutureEq` and to distinct canonical predictive states. This is a
four-variable invariant subsystem; it is not a two-variable autonomous
reduction of arbitrary fine states.

The explicit Euler maps and synchronized identities are formalized for
arbitrary real step size. The failure of pair-mean descent and the distinct
predictive-state witnesses require a nonzero step size. The results do not establish numerical stability, convergence
to an ODE solution, continuous-time existence or uniqueness, or an
infinite-space evolution. The cubic field is separately chosen; no
variational derivative of the repository's planar elastica functional is
replaced by an assumed formula.

**Completed local verification**

| Check | Status | Evidence and limits |
|---|---|---|
| New-module standalone Lean checks | PASS | The component harnesses were checked with `lake env lean --trust=0`. The nonlinear harness uses the actual finite graph fragment and the existing `FutureObservations.inc`. |
| New-module axiom audit | PASS | Reported dependencies are restricted to the permitted Lean foundations `propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `admit`, custom axiom, or `native_decide` is introduced. |
| Independent review | PASS | The completed independent review found no blocking mathematical or integration defect in the reviewed extension. This is review evidence, separate from compilation. |
| Repository tests | PASS | [integration-repository-tests.log](../../verification/integration-repository-tests.log): `Ran 241 tests in 43.049s`, followed by `OK`. |
| Exact finite Laakso checker | PASS | [laakso-finite.json](../../verification/laakso-finite.json) and [checker log](../../verification/integration-check_laakso_finite.log); details below. |
| Unified integration run | PASS | All 27 stages exited zero, including source audit, repository tests, finite checks, offline ARC checks, the joint Lean audit, MovingCurve, Okanohara transport, and finite Markov transport. [pr-integration.json](../../verification/pr-integration.json) |
| Repository-wide theorem and declaration counts | PASS | The fresh combined report records 4,732 theorems and 6,308 declarations; all declarations have a complete axiom audit, and the original declaration axioms remain unchanged. [main-result.json](../../verification/main-result.json) |
| Canonical reader rendering | PASS | `tools/render.py` regenerated the readers, including 1,306 expressions in the main reader and 48 in the verification reader. The Laakso section is present, and no math placeholder remains in the main reader. |
| Clean dependency rebuild | Not performed | Existing package caches are shared and build artifacts were copied into the new worktree. |
| Remote CI on a published exact commit | Not claimed | The local source state is dirty and is identified by source hashes. |

The exact finite checker is
[tools/check_laakso_finite.py](../../tools/check_laakso_finite.py). Its saved
result reports the following graph instances:

| Level | Vertices | Labelled edges | Cycle rank |
|---:|---:|---:|---:|
| 0 | 2 | 1 | 0 |
| 1 | 6 | 6 | 1 |
| 2 | 24 | 36 | 13 |
| 3 | 120 | 216 | 97 |
| 4 | 672 | 1296 | 625 |

It reproduces the mean-obstruction witnesses using exact rational arithmetic
at coupling values `-2`, `0`, `1`, and `7/3`, checks 36 synchronized step
instances, and rejects both mutation controls: omitting a parallel edge and
replacing the required vertex masses by unit masses. Its recorded script
SHA-256 is
`d758dfc5ea32033fe375a324ab96e9b2471900e1d3b24b5ee39dfe154d433efb`.
These computations are finite rational instances. The all-real-coupling and
all-finite-iteration claims come from the Lean theorems, not from extrapolating
the sampled checks.

**Environment, failed attempt, and provenance**

The worktree is based on upstream main commit
`28721702d21720c37805fb64924253f3e1ace11f`. The checked extension is a local
dirty source state on top of that base; the base hash alone does not identify
the tested changes. The companion results JSON records source hashes and
verification outputs for the actual files. Neither this record nor a local
successful run should be presented as a successful remote CI run at the base
commit or at an unverified later commit.

The pinned Lean toolchain is `leanprover/lean4:v4.30.0-rc2`. The mathlib
revision is `5450b53e5ddc75d46418fabb605edbf36bd0beb6`, as recorded in
[lean/lake-manifest.json](../../lean/lake-manifest.json). The task-local
`.venv` uses Python `3.14.5`, pytest `9.2.0`, and NumPy `2.5.4`. Shared package
caches and copied build artifacts support this local run; no fresh build of
all dependency sources is claimed.

The first unified attempt failed in repository test discovery because
`tests/test_elliptic_modular_probe.py` imports pytest and the selected Python
environment did not have it installed. The original failure is preserved in
[verification/laakso-failed-missing-pytest-20261114](../../verification/laakso-failed-missing-pytest-20261114/),
including its repository-test log, integration stdout log, and integration
JSON. The error was `ModuleNotFoundError: No module named 'pytest'`. That
failed attempt is retained separately from the subsequent 241-test passing
run; it is not overwritten or described as a successful verification.

The supported orchestration entry point remains
[tools/verify.py](../../tools/verify.py). The unified integration command is
`python -B -X utf8 tools/verify.py --integration-only`, run with the task-local
virtual environment. It completed with exit code zero. The source-hash-bound
JSON companion retains the successful run and the separately preserved
failed attempt; it does not relabel either as remote CI evidence.

Research materials are read-only sources. Their saved Python demonstrations,
hand arguments, and prior verification reports are distinct from the new
Lean proofs and the finite computations recorded here. No Research original
is changed by this extension.
