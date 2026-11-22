# Proof Forge applied to actual observer-orientation research (2026-11-22)

Parent tool: draft PR #196 (pinned Lean/Mthlib, exact-head, fail-closed
certificate generation, no automatic merge).

This continuation is an executable bridge from
[2026-11-11-observer-orientation-depth.md](../research/2026-11-11-observer-orientation-depth.md)
and [tests/test_operator_orientation_depth.py](../../tests/test_operator_orientation_depth.py)
to the Proof Forge request schema. **The 3- and 4-state examples reproduce
earlier research; they are not newly discovered theorems.**

## Actual archived research cases

| Data input | States | Operator alphabet | Pair | Exact outcome |
| --- | ---: | --- | --- | --- |
| orientation_old_alphabet | 3 | identity | (0,1) | No finite word distinguishes |
| orientation_extended_alphabet | 3 | identity, fresh (0,2,2) | (0,1) | Shortest word [1] |
| orientation_primitive | 4 | u=(0,2,3,3) | (0,1) | Shortest word [0,0] |
| orientation_macro | 4 | u, u²=(0,3,3,3) | (0,1) | Shortest word [1] |

The external research test independently recomputes **all 16 ordered
state pairs** under the primitive/macro vocabularies, cross-checks the
existing breadth-first reference oracle, and confirms that adding u²
shortens some minimal named-word lengths without changing which pairs are
distinguishable. A new primitive can refine the observational quotient;
a compiled macro in the same semigroup does not.

## New nontrivial hidden-history extension

To test a genuinely **nontrivial quotient** instead of the four-state
example where all four original states eventually separate, construct the
eight-state system with state (base, hidden) in
{0,1,2,3} × {0,1}, encoded as base+4*hidden.

Its readout forgets hidden. Its primitive u and compiled u² keep the
hidden coordinate unchanged and apply the original four-state transitions
to the base coordinate.

Proof Forge certifies:

- \`orientation_hidden_primitive\`: (0,1) first distinguishes after **2**
  primitive actions.
- \`orientation_hidden_macro\`: (0,1) first distinguishes after **1**
  named macro action.
- \`orientation_hidden_quotient\`: (0,4), which differ only in hidden
  coordinate, cannot be distinguished by **any finite word** of primitive
  or macro actions. The generated Lean theorem quantifies over all words.

An independent exhaustive Python comparison of all **64 ordered pairs**
confirms that the predictive equivalence relation is exactly equality of
base coordinates, producing 4 quotient classes, each of size 2. Thus
the quotient is unchanged by adding the compiled macro even though the
minimal named-word depth is not.

| Separating length | Primitive only (64 ordered pairs) | Primitive+macro |
| --- | ---: | ---: |
| Unseparable | 16 | 16 |
| 0 | 24 | 24 |
| 1 | 16 | 24 |
| 2 | 8 | 0 |

This table is **finite Python enumeration**, not itself an independently
Lean-proved all-pairs classification. The three specified hidden-state
cases *do* receive generated Lean certificates, including unbounded
indistinguishability for (0,4). Keep this distinction explicit.

## Commands and evidence

The new Proof Forge CI step runs:

~~~sh
python -m unittest discover -s tests -p 'test_proof_forge_orientation_research.py' -v
~~~

The normal Proof Forge workflow then generates all certificates from the
JSON request files and compiles them at the exact proposed commit with
repository-pinned \`--trust=0\`, auditing \`#print axioms\`. The machine-readable
reports include SHA-256 source identities, results, audit status and logs.
A failing compilation MUST leave the corresponding result unverified.

## Interpretation and limitations

This is about **observer-relative predictive indistinguishability**, not an
absolute time parameter. Compiling two primitive transitions into a single
named macro changes the shortest *symbolic word length* but not necessarily
any physical time. Hidden states can survive observation without being
recoverable; their identification depends on the chosen transitions and
readout. No statement about actual physical spacetime, cognition, or
general infinite-state processes follows from the finite experiments.

Safety: no API spending, no unattended agent-written Lean commands, and
no main auto-merge. The Lean kernel job runs with read-only credentials;
a separate post-success job has narrowly scoped attestations and OIDC
permissions to sign the evidence ZIP without checking out PR source.
