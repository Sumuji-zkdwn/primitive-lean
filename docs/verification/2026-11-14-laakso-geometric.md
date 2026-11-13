# Geometric Laakso tower extension — verification record, 2026-11-14

This extension realizes the existing labelled finite Laakso graphs by closed
real intervals, defines their continuous surjective ternary bonding maps,
and instantiates the existing compatible-sequence inverse limit with these
actual geometric levels. The three new modules contain **56 theorems and
89 declarations**. These are extension counts, not repository-wide counts.

The machine-readable companion is
[2026-11-14-laakso-geometric-results.json](2026-11-14-laakso-geometric-results.json).
The unified local integration run **passed all 28 stages**. The combined `--trust=0` compilation checked **4,788 theorems and 6,397 declarations**, with zero warnings, no unexpected axioms, and unchanged baseline declaration axioms. All **420 proof-input hashes** were rechecked after completion. The combined compilation took 438.857 seconds; the sum of integration stage times was 777.242 seconds. This records the local precommit working-tree run, with the cache and source-binding conditions below; it is not a remote CI claim.

| Module | Declarations / theorems | Formalized scope |
|---|---:|---|
| [LaaksoRealization.inc](../../linear_input/lean_check/LaaksoRealization.inc) | 25 / 16 | Quotient of closed edge intervals by the kernel of endpoint normalization; distinct parallel-edge interiors; compatible map descent and continuity; compact realizations of finite graphs. |
| [LaaksoGeometricProjection.inc](../../linear_input/lean_check/LaaksoGeometricProjection.inc) | 23 / 18 | Explicit thirds formula on the actual refinement, endpoint compatibility, continuous surjective bonding, an interior noninjectivity witness, and an affine coordinate-difference identity. |
| [LaaksoGeometricTower.inc](../../linear_input/lean_check/LaaksoGeometricTower.inc) | 41 / 22 | Recursive discrete index topologies; compact finite levels; actual continuous surjective bonding; compatible threads; a homeomorphism of level zero with the unit interval; continuous surjective interval evaluation; and coherent pulled-back height. |

The topology on each realization is the quotient topology from the raw
disjoint union of vertices and closed intervals. The topology on `Tower`
is the subspace topology inherited from the product of its levels.
`baseHomeomorph : Space 0 ≃ₜ unitInterval` identifies the base realization
with the closed unit interval. Choice selects preimages to construct
`threadFromBase` and the injective `intervalThread`; **continuity of these
chosen maps is not asserted**. The interval evaluation itself is continuous
and surjective. `heightAt` is defined by pulling back the base coordinate
through the bonding maps and agrees on every compatible thread.

This extension does not establish a path metric, global Lipschitz bound,
measure, measure pushforward, Hausdorffness or path connectedness of all
levels, compactness or metrizability of the entire inverse limit, Hausdorff
dimension, Ahlfors regularity, or a Poincare inequality. Nor does it prove
that the earlier nonlinear reaction commutes with all geometric bonding
maps. The fuller theorem-to-text correspondence is in
[geometric.md](../laakso/geometric.md).

**Verification evidence**

| Check | Status | Evidence and limits |
|---|---|---|
| Development component standalone Lean checks | PASS | The completed component harnesses passed before final integration; these checks are component evidence. The authoritative full combined result is the unified integration result below. |
| Component axiom reports | PASS | The retained realization, projection, and final tower audit reports use only the permitted foundations `propext`, `Classical.choice`, and `Quot.sound`. The completed global all-declaration audit independently confirms the same bound. |
| Independent final source review | PASS | Review found no blocking defect in the final reviewed source. Review is separate from compilation. |
| Repository tests | PASS | [integration-repository-tests.log](../../verification/integration-repository-tests.log): `Ran 241 tests in 45.689s`, followed by `OK`. |
| Exact geometric rational checker | PASS | [laakso-geometric.json](../../verification/laakso-geometric.json), with seven rejected mutations; finite scope below. |
| Canonical reader rendering | PASS | Exit zero; [render log](../../verification/laakso-geometric-render.stdout.log) and [render.json](../../verification/render.json) record 1,310 expressions in the main reader, 48 in the verification reader, and 0 in the former linear-input reader. |
| Unified integration | PASS | [pr-integration.json](../../verification/pr-integration.json): all 28 stages completed with exit code zero. |
| Repository-wide counts and all-declaration axiom audit | PASS | [main-result.json](../../verification/main-result.json): 4,788 theorems, 6,397 declarations; zero warnings or unexpected axioms. |
| Proof-input hashes after completion | PASS | [results companion](2026-11-14-laakso-geometric-results.json), `83bd6e7f9df8cb11438a61e6570620c440f16c19097673df6ab1f9d1a847bc5c`, all 420 recorded inputs match current bytes. |
| Clean dependency rebuild | Not performed | Existing package caches are shared and build artifacts were reused/copied. |
| Remote CI at an exact published commit | Not claimed | This record concerns a local source-hash-identified working-tree run. |

The independent checker reuses the finite graph builder but implements its
own exact rational point normal form and bonding calculations. It checks
the four maps from levels 1 through 4 to levels 0 through 3. Only endpoints
are identified with vertices; interiors retain their edge IDs.

| Rational instance check | Count |
|---|---:|
| Endpoint compatibility | 3,108 |
| Refined vertex height | 822 |
| Refined edge sample height | 10,878 |
| Edge-length-scaled coordinate-difference identity | 32,634 |
| Distinct sampled surjectivity targets | 2,224 |
| Distinct sheet-point pairs with equal images | 259 |
| Rejected mutations | 7 |

Forgetting the third offset fails at all four levels. Collapsing parallel
edges by their endpoint pair fails at the three tested levels containing
parallel edges. The current checker SHA-256 is
`63ffb662a002e0dcfdff3f4a9bd86911d7ef304e8e34ec505c4d2037adb09ba7`;
its shared finite builder SHA-256 is
`d758dfc5ea32033fe375a324ab96e9b2471900e1d3b24b5ee39dfe154d433efb`.
These computations do not prove continuity, an all-real fiber formula, or
any global path-metric assertion. The all-real continuity and surjectivity
claims are supplied separately by the Lean theorems.

**Environment, retained failures, and provenance**

The base commit is `583e9d1dcb1e7e215082131e9c82cc65905bbd12`.
The checked changes are a local working-tree state above that base;
the base commit alone does not identify the checked extension. The final
source ledger is [provenance-geometric.json](../laakso/provenance-geometric.json).
Its three module hashes matched the actual source files during the completed post-run audit:

| Module | SHA-256 |
|---|---|
| `LaaksoRealization.inc` | `c4dca8a0b519516128aae8e6b6cd7254c17fa57b3ca21e6c2ba29b80dec32b16` |
| `LaaksoGeometricProjection.inc` | `7ed41c14e6ce22e77158ca77bee7520eae9309e0220a5d87241aa5c351aa32f4` |
| `LaaksoGeometricTower.inc` | `29384eefe606d2368a0961cc391a380d1e8418eb74bcd7bfa8f01484def1e62e` |

The pinned toolchain is `leanprover/lean4:v4.30.0-rc2`; the mathlib revision
is `5450b53e5ddc75d46418fabb605edbf36bd0beb6`, from
[lean/lake-manifest.json](../../lean/lake-manifest.json). The reused
task-local Python environment is the sibling first-stage checkout's
`.venv`, with Python `3.14.5`, pytest `9.2.0`, and NumPy `2.5.4`.
The geometric checker itself uses the Python standard library only.
The package directory is a junction to an existing package cache, and
existing build artifacts were reused/copied; no clean dependency rebuild
is claimed.

Earlier component elaboration failures are retained outside the repository
in `../geometric_staging/`, relative to the worktree root. In particular,
`realization_compile.log` records initial noncomputable-definition and
argument-shape errors; `tower-first.log` and `tower-second.log` record
unsolved goals; and `tower_debug.log` retains intermediate rewrite errors.
Warnings about synthesized `sorry` in these failed elaborations belong to
those failed attempts, not to accepted proof evidence. The later component
reports are `realization_axiom_audit.log`, `projection/axiom-audit.log`, and
`tower_final_audit.log`. These local retained logs are not represented as
successful integration logs or as published remote artifacts.

The authoritative orchestration entry point remains
[tools/verify.py](../../tools/verify.py):

```console
python -B -X utf8 tools/verify.py --integration-only
```

Its final exit status is **0**. The successful
component checks do not substitute for that complete run. The results companion binds this run to the post-run source hashes. Earlier failed
component attempts remain separate from the completed integration run. Research originals remain read-only sources, with their
inherited provenance retained in [provenance.json](../laakso/provenance.json).
