# Minimal observational core for Forge

Shadow research stacked on #295. Replace cardinality maximization as the
controller's objective by exact behavioral minimality under the current
external model. This is a deterministic finite-state prototype, not a
general solution for arbitrary computation, scientific inference, or
globally smallest program descriptions.

## Contract

The environment supplies a finite set X={0,...,n-1}, named observation
tables K_i, and named action tables T_a:X->X. Let K be their tuple.
For a word w of arbitrary finite length, T_w denotes successive application.
Define x~y iff K(T_w(x))=K(T_w(y)) for every w (including the empty word).
Keep X/~ as the controller's behavioral state representation.

The algorithm starts from the observation partition and repeatedly
refines each block using the tuple of successor block IDs for every action.
The partition after r rounds is equality of observations for all words
of length at most r, by induction. Each nonstable round strictly raises
the block count, so it stops in at most n-1 strict rounds. At the fixed
point, observations and each action descend to the quotient; induction
on word length then proves agreement for all finite words. This is
the coarsest observation-respecting stable partition. Any deterministic
representation of all original states preserving all observation traces
must separate every pair with a distinguishing word, so it requires
at least as many states as this quotient. The conclusion is classical
mathematics; not a Lean-checked general theorem in this PR.

An independent reverse BFS on unordered pairs finds exactly the pairs
with a finite distinguishing word, with shortest witnesses. Each update
checks equality of its quotient partition with that independent relation
on *every* pair, and checks quotient action/observation well-definedness.
Witnesses are retained for new distinctions, not all pairs.

## Conservative extension

New observation/action tables and new raw states may be appended. Existing
tables must agree on all old states; old actions therefore still map the
old subset into itself. This makes previous distinguishing words valid
forever. For the same raw set, refinement can safely start from the
previous stable partition. With new states, recompute from observations
so equivalent new and old states may merge. The number of quotient
classes never decreases for these conservative additions, but does
not increase unless a new distinction exists. Changing or removing old
observations/actions is outside this monotone contract.

For restart, keep only a current checkpoint (schema, external model digest,
and canonical state-to-block map). The previous external model is supplied
separately and replayed to reject tampering. Do not accumulate all prior
models, all words, or all candidate operators in the controller checkpoint.
The quotient transition table and split witnesses are derived reports.
The external model and its complete action vocabulary are still required;
the checkpoint does not claim to be a globally minimal encoding, and
discarding redundant external actions might be unsound under future
extensions. Pair-BFS auditing is intentionally independent and not a
minimum-memory algorithm.

## Verified local tests

- 8 raw states, cycle, no observer: 1 quotient class.
- Parity: 2. Mod-4: 4. Redundant parity: still 4.
- Swap 0/1: 8. Identity: still 8.
- Append a ninth raw state equivalent to state 0: still 8.
- Add a marker separating the ninth raw state: 9.
- All 216 three-state binary observers/single-action models checked
  against explicit traces of lengths 0,1,2 as well as the pair oracle.
- A noninjective action requires a length-two distinguishing witness.
- New-only classes, invalid checkpoint, removed observation, and idempotent
  replay are tested.

A read-only CI demo reconstructs the pinned four semantic receipts and six
evolution receipts from #292, then progressively exposes the real 256-state
alphabet using a parity observer. It uses finite snapshot replay, not
new Lean certificates or production admission. The current production
alphabet and ledger are unchanged.

## Reproduction

```sh
python -B -m tools.autonomy.forge_minimal_core --selftest
python -B -m tools.autonomy.forge_minimal_core --forge-demo --state tests/fixtures/forge_monoid_evolution6.json --semantic tests/fixtures/forge_monoid_semantic4.json
python -B -m tools.autonomy.forge_minimal_core --model model.json --output verification/minimal-a
python -B -m tools.autonomy.forge_minimal_core --model next-model.json --previous-model model.json --resume verification/minimal-a/checkpoint.json --output verification/minimal-b
```

Input model format: {"n":2,"observations":{"parity":[0,1]},"actions":{"swap":[1,0]}}.
Bounds: 256 raw states, up to 32 observations and 32 actions, 2 MB JSON.
The prototype fails closed beyond its bounds. New symbolic or stochastic
models require a distinct reviewed proof layer; no claim of indefinite
growth beyond finite budgets. No changes to main, production ledgers,
existing workflows or autonomous schedules. The next practical step is
an external problem-driven candidate source with a separately verified
admission criterion.
