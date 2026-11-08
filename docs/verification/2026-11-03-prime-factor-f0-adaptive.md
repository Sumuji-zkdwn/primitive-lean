# Verification record: finite prime-factor F0 and adaptive observations

Date: 2026-11-03 (JST).
Draft PR: https://github.com/Sumuji-zkdwn/primitive-lean/pull/52
Independent proof-source commit: 829f3e8cc8602894acb522b1e8fcd5424e9d3738
Successful GitHub Actions: https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41628166301
Source: linear_input/lean_check/PrimeFactorF0Adaptive.inc
Workflow: .github/workflows/prime-factor-f0-adaptive-probe.yml
Compile command: lake env lean --trust=0 PrimeFactorF0AdaptiveProbe.lean

## Domain and observation library
Exactly three factor positions, each containing one of the coded primes 2,3,5.
State count: 27 ordered triples. The only permitted probes are product, first factor, second factor.
Every call returns its full defined output and costs one unit, independent of internal computation.

## Confirmed Lean statements
- normalize_is_sorted: every normalized triple is nondecreasing.
- normalize_of_sorted: every sorted triple is fixed.
- normalize_idempotent: the normalization is an idempotent map.
- normalize_preserves_product and normalize_preserves_bag: normalizing changes neither product nor unordered multiset.
- product_kernel_eq_normalize_kernel: product equality iff normalized-state equality.
- normalize_kernel_eq_orbit: the same kernel equals the six-permutation orbit relation of PR #51.
- normalize_fixed_iff_sorted and normalize_fixed_point_count: the ten fixed points are precisely sorted triples.
- canonical_of_surjective: retraction onto typed canonical representatives.
- factors_through_normalize_iff: a probe factors through normalization iff it is constant on product fibers.
- joint_normalize_product_same_kernel: product adds no distinguishability after normalizing.
- first_factor_not_recoverable_from_normalize: the first-factor observation does not descend through F0; uses PR #36 no_factor_of_separation.

## Adaptive observation depth
Define adaptiveTwo(first, choose, x) as the pair of the first observation and a second observation whose probe index choose(value) depends on the first output.
- hard_fiber_second_probe_collision: any selected first probe has a concrete first-answer fiber such that every possible second probe collides on that fiber.
- adaptive_two_not_injective: for EVERY first index and EVERY function choose : Nat -> Fin 3, the two-call transcript is noninjective.
- adaptive_three_upper_bound: the fixed three calls [product, first, second] separate all 27 states.
Thus worst-case observation depth is exactly three in this restricted deterministic adaptive protocol model.

## Trust and explicit limits
The standalone job compiles unchanged PR #36, #50, and #51 sources, plus only the new module, using the pinned toolchain.
The new module is screened for sorry, admit, axiom, unsafe, native_decide, and compiled with Lean --trust=0.
The SIX targeted #print axioms outputs contain only propext, Classical.choice, Quot.sound.
This is targeted principal-theorem inspection, NOT a repository-wide axiom audit.
F0 here means a finite idempotent forgetting map, not a claim of equality with any other existing LinearInputF0 map.
No result proves general integer unique factorization, unrestricted observation complexity, runtime complexity, or n-factor behavior.
