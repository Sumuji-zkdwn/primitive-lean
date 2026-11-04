# State-resident higher-order lift rewriting

Date: 2026-11-04. Follow-up to PR #64, based on verified commit 48855cedf7e8723b458e0f25c90121d1c5b115fa.

## Model

The state extends PR #64's (known, edges, metaRules) with liftRules and liftEdits. A newly acquired operator can activate an edit in the state and append a rule to liftRules. The fixed interpreter executes the updated liftRules to produce metaRules, then compiles those metaRules into object edges.

The Fin 4 witness reproduces the lower-level trace of PR #64: known operators progress from [0] to [0,1,2,3], and then the finite frontier saturates. The frozen-meta control stops at [0,1,2].

## Separate observations

The prototype checks liftRules mutation directly: the table changes from empty to one rule after learning operator 1. Separately, it measures the distinct one-step object-target sets over known operators. The frozen control has 3 observation classes; the PR #64 second-order run and the higher-order run each have 4. This is one explicit finite observation quotient, not a universal operator-identity claim.

## Boundaries

The interpreter and the bootstrap edit table remain fixed. This is state-resident finite rule rewriting, not unrestricted self-programming. The example saturates at four descriptors and proves no unbounded extension.

## Verification

The new Python regression is included in the integration workflow. The exact Lean declarations are added to the supplemental source set and subject to the existing all-declaration axiom audit. Lean and Mathlib execution must be judged by the new GitHub Actions run for the proposed head.
