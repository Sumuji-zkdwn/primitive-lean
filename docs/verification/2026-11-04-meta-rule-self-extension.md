# Second-order self-extension of finite operator rules

Date: 2026-11-04. Additive research branch stacked on verified PR #63.

## Aim
PR #62 allowed a fixed object-level generator to reprocess the newly acquired
operator descriptors. PR #63 made the object-level generation rule table
mutable, but the compiler from descriptors to new rules stayed fixed.

This module makes the **meta-rule table** mutable as well. An acquired
descriptor can introduce new meta rules, which change how subsequent
descriptors compile into object-level rules. The separate higher-order
`lift` remains **fixed**: it is not a universal self-writing interpreter.

## Exact machine state and updates
A `MetaMachine α` has three lists:
- `known`: registered one-point operator-patch descriptors.
- `edges`: current object-level generation rules `source -> target`.
- `meta`: current second-order rules `descriptor -> object edge`.

`metaStep lift viable s` chooses the first viable, as-yet-unseen target
from the current **object-level** frontier. It appends this target to the
operator catalogue, appends those object edges selected by the **current
meta table**, and appends the higher-order lift's outputs to the meta table.

Every successful update is thus `(K,R,M) -> (K+[a], R+M(a), M+L(a))`.
All of the lists are retained without deletion; their entries are not
claimed to be pairwise distinct except for each accepted new target.

## Formal statements
- `metaStep_sound`: every new descriptor is generated from the current
  object frontier, previously unknown, viable, and the update is exact.
- `metaStep_complete`: a viable new object-level descriptor is enough
  for a successful step.
- `metaStep_none_certificate`: a failed step means the current frontier
  contains no viable candidate. It says nothing about unlisted candidates.
- Strict catalogue growth and retention of all old operator descriptions,
  object rules, and meta rules.
- `divergent_next_edges_require_meta_difference`: holding the operator
  catalogue, object-level rules, viability, and higher-order lift fixed,
  different newly produced object rules require different meta-rule tables.
- `meta_repair_survives`: conditional connection to PR #60's terminal
  local-extinction obstruction; successful generated patch is necessary
  relative to the specified old operator vocabulary.
- Bounded `iterateMeta` and no-change-after-saturation theorem.

## Finite control and countermodel
A four-descriptor machine begins with known `[0]`, one object edge `0->1`,
and one meta rule `1 -> (1->2)`.

The first learning step acquires 1. Its predefined higher-order lift installs
**new meta rule** `2 -> (2->3)`. The second learning step acquires 2,
which now generates the object edge `2->3`. The third step acquires 3.

The **frozen-meta control** shares exactly the same known list `[0,1]` and
object-rule list `[0->1,1->2]` after the first step, but does not have the
new meta rule. Both controls acquire descriptor 2, yet only the updated
meta machine installs `2->3`; the frozen machine subsequently stops.
This isolates the causal role of the second-order rule update.

## Boundaries
A fixed lift maps learned descriptors to new meta-rule data. Its code and
the state type are not modified. This is finite bounded second-order
self-extension, not unlimited recursive novelty, autonomous invention of
a new higher-order interpreter, or a claim about actual cognitive/physical
worlds. A new descriptor is not automatically a new observational quotient.
Local extinction, terminal feasibility, and conservation are separate
hypotheses.

## Verification
Source: `linear_input/lean_check/MetaRuleSelfExtension.inc`
Namespace: `LinearInputMetaRuleExtension`.
Regression: `tests/test_meta_rule_self_extension.py`.
`python -B -X utf8 tools/verify.py --integration-only` with pinned
`lake env lean --trust=0`, full all-declaration axiom audit and source
provenance hashes. No new Lean statement is counted proved before a
successful exact-head CI run. Prior source modules are unchanged.
