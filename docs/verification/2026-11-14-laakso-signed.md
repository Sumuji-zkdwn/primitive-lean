# 2026-11-14 Laakso signed connection verification

This record covers the first six-edge Laakso approximant with a one-edge
sign flip and the Research two-component energy at lambda=kappa=1, u=0.
The exact model and theorem map are in [signed.md](../laakso/signed.md).
The local source ledger is [provenance-signed.json](../laakso/provenance-signed.json).

**Local integration completed successfully.** All 29 stages exited zero,
including 241 repository tests, the finite signed checker, the joint Lean
assembly and the independent retained modules. The completed assembly contains
**4,830 theorems and 6,460 declarations**, including
**42 new theorems and 63 new declarations** in the two signed modules.
The trust-zero compilation reported no warnings or unexpected axioms; the
baseline declaration axioms matched. All 422 recorded
proof-input hashes and all 6,460 raw axiom outputs
were rechecked after completion.

| Check | Result and evidence |
|---|---|
| Unified integration | PASS, [pr-integration.json](../../verification/pr-integration.json), 29 stages |
| Joint proof and full axiom audit | PASS, [main-result.json](../../verification/main-result.json) |
| Signed finite replay | PASS, [laakso-signed.json](../../verification/laakso-signed.json) |
| Source preservation and native registration | PASS, [provenance-signed.json](../laakso/provenance-signed.json) |
| Post-run evidence and source binding | PASS, [results companion](2026-11-14-laakso-signed-results.json) |
| Canonical reader rendering | PASS, [render.json](../../verification/render.json), 1,315 / 48 / 0 math expressions |
| Clean dependency rebuild | Not performed; shared package cache and copied build outputs |
| Remote CI | Not claimed by this local record; exact published-head CI is separate |

The result companion SHA-256 is
`4862cc0faa0ff61392bd017ae3010f193e22f192011c447fce337ae6a95f66e5`.
The combined proof compilation took 526.528 seconds;
the sum of integration stage times was 904.258
seconds. The final orchestration exit status was 0. This is a local precommit
working-tree run, identified by the complete source hashes in its companion.

| New source | Declarations | Theorems | SHA-256 |
|---|---:|---:|---|
| `LaaksoSignedConnection.inc` | 40 | 24 | `c117e42c6a26129259aba01d79d3c3ebc2b0811f08bf133a4c03cd1e99211459` |
| `LaaksoSignedEnergy.inc` | 23 | 18 | `c3714d5eddb67214a8f2c76dae3cad78a592f9aa2a88ba15cb43215a828b82e9` |

The independent checker enumerates 64 signatures and 64 spins per
signature, with 4,096 exact well-state energy evaluations. It also checks
the lower-bound certificate and flip-difference polynomial by rational
coefficient identity, and evaluates 69 rational state samples. Four mutation
controls reject dropping parallel edges, identifying connected lift
vertices, ignoring the sign change, and omitting the coupling factor 1/2.
These checks do not establish a continuous-state minimum or a dynamical
claim. The all-real lower bound is proved separately in Lean.

The preserved Research source and original have SHA-256
`f70c840823a161ee068e3ca805b01a7b2e4b12d7ad8a0a3a714cf8d79006140a`.
The base commit is `9ad1fe7e0505d0e9507ed6bf231100955928a55b`.
The local checked extension is identified by its source hashes, not by
the parent commit alone. The toolchain remains Lean v4.30.0-rc2 and mathlib
5450b53e5ddc75d46418fabb605edbf36bd0beb6. Existing package caches are shared
by a junction, and build outputs were copied from the preceding verified
worktree. This is not a clean dependency rebuild.

Failed initial component elaborations are retained in the parent task's
`signed_staging/signed/` and `signed_staging/energy/` directories. They are
separate from accepted verification evidence. No Research original was
edited. The canonical entry point remains:

```console
python -B -X utf8 tools/verify.py --integration-only
```

An independent finite replay is available with:

```console
python -B -X utf8 tools/check_laakso_signed.py
```

It writes `verification/laakso-signed.json` by default, or the supplied
`--output` path. Proof compilation uses `--trust=0`; the permitted axioms
are only `propext`, `Classical.choice`, and `Quot.sound`.
