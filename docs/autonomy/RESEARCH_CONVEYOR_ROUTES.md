# Research Conveyor: reviewed multi-domain finite adapters (2026-11-23)

These are finite experiments selected from previously reviewed definitions.
The original research statements do not become theorems just because a
derived finite model compiles.

## Design contract

Each route has a source path, the current exact SHA-256 in each
receipt, a **pinned reviewed Git blob identity**, a specific
source-line anchor, a finite transition-table constructor, and an
explicitly limited claim. The Laakso adapter additionally pins both
the underlying Lean first-level finite-graph source and the independent
Python finite checker's Git blobs. **Any byte change requires explicit
adapter review before the next run.** The result ledger is updated *only after*
GitHub-hosted Lean kernel compilation with --trust=0 and an axiom audit.

Routing is deterministic: at each successful day choose the unfinished
family with the fewest verified receipts. Ties use the fixed sequence
Siphon → observer → Laakso. A dependent experiment is enabled only
when the preceding certificate has the relevant result. No unlimited
model search, AI API call, or unreviewed model-generation code is run.

## Family A: Siphon E (6 tasks, historical adapter retained)

Source: [Siphon predictive quotient](../research/2026-11-17-siphon-predictive-quotient.md).
The already deployed modular F3² adapter is unchanged: E is the chosen
polynomial map, R adds 1 to v, and the readout is u. For each u∈F3,
compare the two states with invariants r=1,2. Old E-only observation
equivalence, when actually Lean-verified, allows the next test with
E and R. The first Siphon record is already preserved in the
persistent state branch and is not duplicated or replayed as new work.

This is a mod-3 statement, not a direct proof of the real-valued source
theorem.

## Family B: observer-relative operation depth (4 tasks)

Sources:
- [Original observer depth research](../research/2026-11-11-observer-orientation-depth.md)
- [Previously kernel-certified example inputs](../../proof_forge/requests/)

The first two are literal, reviewed four-state examples: observations
K=[0,0,0,1], primitive u=[0,2,3,3], initial pair (0,1).

| Task | Allowed operations | Expected all-word result |
| --- | --- | --- |
| observer_primitive | u | shortest [u,u] |
| observer_macro | u, u²=[0,3,3,3] | shortest [u²] |
| observer_hidden | lifted u and u² on 8 states, forgetting hidden bit | (0,4) equivalent for all words |
| observer_visible | same 8-state transition tables, readout additionally observes hidden bit | (0,4) separates at [] |

The macro experiment is scheduled only when the primitive result is a
Lean-certified two-step separator. The visible-readout experiment is
scheduled only when the hidden-bit indistinguishability certificate
succeeded. The final experiment modifies observation, **not** the
primitive operator set.

The eight-state hidden model has states (base,h) with encoding
base+4h, base∈{0,1,2,3}, h∈{0,1}. Its original readout is
K(base,h)=K_base(base). The refined readout is
K_new(base,h)=K_base(base)+2h. Every transition acts on base and
leaves h unchanged.

Named operation count is a language-dependent notion of depth, **not**
physical time and not an intrinsic arrow of history.

## Family C: Laakso raw-vertex observation (3 tasks)

Research source:
[Laakso bonding audit](../research/2026-11-17-laakso-bonding-audit.md).

Algebraic primary sources:
[LaaksoFiniteGraph.inc](../../linear_input/lean_check/LaaksoFiniteGraph.inc),
[check_laakso_bonding_finite.py](../../tools/check_laakso_bonding_finite.py).

The **actual first-level raw states** RawVertex(Fin 2,Fin 1) have
eight members. Encode them, in order, as:

| State | Actual raw meaning | First-stage rawProjection |
| --- | --- | --- |
| 0 | old left, sheet false | L0=0 |
| 1 | old left, sheet true | L1=1 |
| 2 | old right, sheet false | R0=2 |
| 3 | old right, sheet true | R1=3 |
| 4 | W1, sheet false | W1=4 |
| 5 | W1, sheet true | W1=4 |
| 6 | W2, sheet false | W2=5 |
| 7 | W2, sheet true | W2=5 |

The first-stage projected readout is therefore
K=[0,1,2,3,4,4,5,5]. The actual raw
advanceRightGeneral(base) is represented by
U=[0,1,2,3,6,7,2,3]: old vertices stay fixed, each W1 progresses
to W2 on the same hidden sheet, and W2 goes to the corresponding
right endpoint. The inert I=[0,1,2,3,4,5,6,7] is an **additional
stipulated identity action** to construct an old vocabulary; it is not
a canonical new geometric flow.

| Task | Operations | Pair | Expected finite result |
| --- | --- | --- | --- |
| laakso_w1_stop | I | (4,5) | equivalent for all words |
| laakso_w1_advance | I,U | (4,5) | shortest [U,U] |
| laakso_w2_advance | I,U | (6,7) | shortest [U] |

The W1 update certificate is attempted only after verified
invisibility under I. The W2 case is separately checked as a boundary
example. These three experiments formalize **raw-sheet observation
distinctions** and are faithful to the explicitly chosen finite table.

They do NOT establish that advanceRightGeneral descends to a
deterministic function on the six observed vertices: in fact it need
not, because W2's two raw sheets may progress to distinct endpoints.
No claims are made about continuous Laakso dynamics, geometric
bonding under every operation, or an inverse-limit flow.

## Operational evidence

In proposed PRs, the workflow replays an existing authentic Siphon
receipt as a fixture and selects the next observer task, then separately
compiles six representative observer/Laakso certificates in the same
repository-pinned Lean version. Artifacts record their JSON,
generated Lean, stdout/stderr, process codes, SHA-256 and axiom audit.
The smoke input is explicitly labelled unverified until Lean passes.

After merge, the same daily main-only workflow keeps one audited
receipt per UTC calendar day in the separate data-only
autonomy/research-conveyor-state branch. It will stop after its finite
route registry is exhausted; expanding further requires another
source-reviewed adapter and CI.

There are at most 6+4+3=13 receipts under this registry, including
historical Siphon receipts. The previous result is not erased or
reclassified, and no general-theorem status can be written into the
finite-only receipt schema.
