# Persistent Forge Lean Evolution

This is a bounded autonomous extension of the already merged PR #267
(merge commit 50249d37cb1d0d99a8c4e042a9d682b5382c002b). It separates
three responsibilities that were previously missing.

## 1. Persistent certified history

The workflow reads the existing Semantic Foundry data-only ledger and the
new isolated branch `autonomy/forge-lean-evolution-state`, file
`docs/autonomy/forge-lean-evolution-state.json`. It reconstructs the exact
two #267 seed discoveries from the retained actual semantic receipt, then
reruns the four original Lean certificate phases. All new semantic receipts
in the live ledger are independently replayed. The history of evolution
receipts is append-only and hash-linked; each records the exact source
commit, semantic-prefix identity, typed expression, behavior fingerprint,
discovered invariant, explicit witness, theorem name and generated Lean
source SHA-256. Every run reconstructs and kernel-checks historical proofs
before adding another letter. The exact checked source can be reproduced
from the recorded source and data. An incompatible source change fails
closed rather than silently rewriting history.

There are two separate jobs on main: read-only candidate generation and
a write-enabled, independent exact-plan replay. The latter only appends
the verified JSON receipt(s) after rerunning Lean at trust zero, auditing
axioms and comparing every new certificate's source and result bytes. The state branch and live upstream
must still match the original snapshot commits. No main writes, code
generated from state, automatic source changes or new external secrets.

## 2. Automatic invariant discovery

For the current alphabet, partition the 256 states by reachability under
the bijective letters. Also build a graph on all 256 bitwise differences:
there is an edge d -> e if some bijective letter f and some input x satisfy
e = f(x) XOR f(x XOR d). Enumerate closed unary components and closed
nonzero difference components of size at most 8. This searches the
invariants anew, using the actual current tables, not a generation-indexed
list of human-selected invariants.

Each discovered relation R is unary membership (ignoring the second
argument), or membership of the XOR difference in the selected component.
All bijective generators preserve R. All other generators have a
concrete collision. Lean proves for arbitrary words that they preserve R
OR are noninjective, using the finite-set fact that injectivity of a
composition implies injectivity of both factors. For the selected
candidate Lean checks a witness violating R and checks involutivity on all
256 inputs; it derives injectivity and nonexpressibility for arbitrary
old words and arbitrary macro dictionaries using the existing
LinearInputOperatorWords theory. The finite graph search is external to
Lean; the selected invariant's closure and separation are kernel checked.

## 3. Dynamic candidate grammar

Every accepted operator automatically supplies a fresh typed observable
terminal, the output of that operator on an input with one target bit
cleared. The grammar constructs a guard from an output bit and a second
input bit (or the constant one), composed by AND or XOR, and conditionally
toggles the target bit. This is an involution because its guard cannot
depend on the target bit. In every cycle the newest four operator
terminals are expanded, 1024 productions each. The full library grows
even while the active search frontier remains bounded. New guards can
depend recursively on previously admitted operator semantics; no
arbitrary generated Python or Lean source is accepted as a recipe.

The search rejects duplicate finite behavior, looks for an invariant
violation, prioritizes preserving as many other discovered invariants as
possible, prefers even swap count and latest-parent rules, and maximizes
changed inputs within that priority. These are search heuristics, not
proofs of usefulness. The winning map is independently evaluated with
a separate arithmetic implementation and must pass the new Lean
certificate. The report counts actual generated and separating
productions per parent.

## Regression and limits

PR CI uses the actual retained semantic seed and an empty history. It
requires two distinct consecutive generations on different synthetic UTC
dates, byte-identical reconstruction of the first proof on restart,
actual enumeration of the new parent symbol's 1024 productions, no
same-day duplication, and rejection of a corrupted record. A separate
preliminary finite exploration of the exact one-receipt seed vocabulary
found seven initial invariants, four further potential consecutive
extensions, and then no remaining invariant in this bounded family.
Those are finite external observations, not claims of Lean CI success
or live production receipts.

After merge the new workflow runs daily at 14:51 UTC (23:51 JST), on
relevant main pushes, or manual dispatch. Automatic runs append at most
one new receipt per UTC date; a manual batch is the only exception.
The maintenance ceiling remains eight total receipts. If no separator is found it
records explicit bounded exhaustion and does not append invented progress.
GitHub delivery is best effort. This is dynamic expansion within a
reviewed meta-grammar and automatic search within two invariant families;
it is not general automatic invention of arbitrary semantic schemas or
invariants, unlimited mathematical discovery, or self-modifying code.
Existing Generic/Meta/Semantic Forge production ledgers are not modified.

## Group-separation fallback

The legacy unary and small-difference search and its certificate source are unchanged.
Only when it finds no separator, inspect exact membership in the affine and even
permutation supergroups. If all bijective letters preserve the four-point XOR
relation, choose a nonaffine candidate, preferring the canonical Toffoli and
preserving parity. Otherwise, if all are even, choose an odd candidate.
The fallback scans the complete archived parent library; the historical four-parent
frontier and source hashes remain valid for legacy certificates. Each candidate
requires independent finite evaluation, involutivity, and a new kernel certificate
of nonexpressibility even with arbitrary compiled macros. Noninjective letters
cannot occur in a word representing a bijection. The four-point proof uses eight
Boolean linear forms, and the sign proof uses explicit transposition products.
No Python claim about membership in an arbitrary generated subgroup is trusted.
The fallback only tests the stated supergroups, and exhaustion is still bounded,
not a general proof of full symmetric-group saturation. The original eight-receipt
maintenance limit and main-only append gate remain unchanged. PR regression
checks the pinned four-generation sequence, both extension certificates,
byte-identical regeneration and corrupted-witness rejection. No state file changes.

## Manual bounded batch

Select **Run workflow** on main and choose `generations` from 1 to 5
(default 5). Each successful certificate is kernel- and axiom-audited
before its operator enters the alphabet for the next generation. The
read-only plan and separate privileged replay rebuild the entire batch
from identical upstream snapshots; all new certificates and the final
ledger must match byte-for-byte before one atomic JSON-only append.
Exhaustion stops the batch early; proof failure or a changed upstream
snapshot prevents any append from that batch. The eight-receipt total
cap is unchanged. Automatic runs still refuse a second receipt on an
already-used UTC date, including dates with manual receipts.

The schema retains legacy rows byte-for-byte. Manual rows additionally
record the actual GitHub run ID, one-based batch index and requested
limit, covered by the existing receipt hash. Historical replay checks
monotone dates, contiguous same-run indexes, fixed batch provenance and
bounded counts, and reruns every historical certificate. Retrying an
already-recorded run ID is idempotent, even on a different UTC date.
This is not an unrestricted source-modification mode. PR CI covers a
same-date two-generation batch, recursive alphabet reentry, exact
historical certificate replay, retry idempotence, ordinary date gating,
and malformed batch metadata. All PR tests are read-only.
