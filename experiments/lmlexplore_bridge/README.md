# Finite Gibbs free energy: Elastica × LMLExplore

**Decision: RESTRICT — retain an independent, experimental bridge.**
This Lean 4.36 workspace reuses LMLExplore's finite relative-entropy theorems
for a finite indexed family of actual Elastica energy values. It adds a
free-energy gap identity and a unique minimizer on the probability simplex.
The canonical Lean 4.30 proof assembly remains separate.

## Statement and source mapping

Let α be finite and nonempty, set E(a) = Elastica.energy ε (θ a) ℓ, and
let g = curveGibbs β ε θ ℓ. For q in LMLExplore.simplex α, define

    Z = ∑ a, exp (-β * E a)
    g a = exp (-β * E a) / Z
    Fβ(q) = ∑ a, q a * E a + (∑ a, q a * log (q a)) / β
    KL(q || g) = ∑ a, q a * log (q a / g a)

Zero coordinates of q are allowed; 0 * log 0 = 0. The Gibbs coordinates
are strictly positive. For β ≠ 0, the source proves
Fβ(q) = -log Z / β + KL(q || g) / β, hence Fβ(g) = -log Z / β.
For **β > 0**, this gives Fβ(g) ≤ Fβ(q), with equality exactly when q = g.

| Bridge theorem | Content / imported proof |
| --- | --- |
| curveGibbs_apply | Definitional equality with LMLExplore softmax |
| curveGibbs_mem_simplex | LMLExplore.OnlineLearning.softmax_mem_simplex |
| curveGibbs_pos | LMLExplore.OnlineLearning.softmax_pos |
| curveFreeEnergy_eq_neg_log_partition_add_kl | LMLExplore.sum_mul_log_div_mul_exp_div_eq with constant reference weights 1 |
| curveFreeEnergy_gibbs_eq | The Gibbs value is -log Z / β |
| curveFreeEnergy_gap_eq_kl | The free-energy excess is the relative entropy of q with respect to g, divided by β |
| curveFreeEnergy_min | LMLExplore.sum_mul_log_div_nonneg and β > 0 |
| curveFreeEnergy_eq_iff | LMLExplore.sum_mul_log_div_eq_zero_iff and β > 0 |

The only added upstream import beyond the initial softmax bridge is
LMLExplore.InformationTheory.KullbackLeibler.Finite. Its transitive imports
are also built; this does not mean that only one dependency file is compiled.
No additional Elastica module is ported.

## Use in the existing development

The finite-temperature discussion in [the canonical reader, section 8.21](../../原始の形式化.md)
and [CurveWordThermodynamics.inc](../../linear_input/lean_check/CurveWordThermodynamics.inc)
already bounds -log Z / β by the finite minimum and proves its zero-temperature
limit. The new curveFreeEnergy_gibbs_eq identifies that same scalar formula
as an attained minimum over probability vectors on the indexed curve family;
the gap and equality theorems characterize its minimizer.
The independent workspace does not import the old CurveWordThermodynamics
assembly or claim to recheck its theorems under Lean 4.36.

[FiniteBayes.inc](../../linear_input/lean_check/FiniteBayes.inc) already proves
curve_weight_distribution for arbitrary prior distributions and
curve_split_update using the actual Elastica interval-splitting theorem.
The first three bridge theorems therefore establish interoperability, rather
than a previously missing ability to normalize curve weights. The additional
result here is the KL characterization of the entropy-regularized minimum.
It is a specialization of known mathematics, with no novelty claim.

The minimization is over probability vectors on a **fixed finite indexed
family**, not over all admissible curves. Distinct labels may denote the same
curve; uniqueness concerns the probability vector on labels. No physical
probability model, smoothness/admissibility of the candidates, continuous-curve
minimizer, dynamics, or online-learning regret guarantee is inferred.

## Compatibility boundary and decision

prepare_compat.py verifies the Git blob hash of the original
lean/Elastica/Variation.lean and generates an isolated compatibility copy.
Exactly one proof tactic in a dominated-differentiation lemma changes. The
original definitions, statements, hypotheses and source file are retained.
The original energy definition is an interval integral of signed-curvature
density. No sign assumption on this energy is required for the finite result.

The earlier attempt to port the full Elastica.ExponentialWeight and
constrained-variation stack was unsuccessful; its failed CI history remains
in PR #138. This reduced bridge does not import Elastica.exponentialWeight
or claim a wholesale merger of the two theorem collections.

The bounded experiment succeeds if the gap, value, minimum and uniqueness
results build with the pinned dependencies and pass kernel/axiom checks,
without adding an Elastica compatibility module or upgrading the main toolchain.
Further integration remains **RESTRICT**. Stop if it requires those broader
ports or has no concrete use in the existing mathematical exposition.

## Reproduce and audit

    cd experiments/lmlexplore_bridge
    lake update
    python3 prepare_compat.py
    lake exe cache get
    lake build ElasticaLMLExploreBridge
    lake env lean --trust=0 ElasticaLMLExploreBridge.lean
    python3 check_axioms.py --self-test
    python3 check_axioms.py

The audit recompiles the current bridge source with --trust=0 and prints
the axioms of all eight bridge theorems. Only propext, Classical.choice
and Quot.sound are allowed; sorryAx, extra axioms, and missing or duplicate
theorem records fail the audit. Its parser has positive and negative fixtures.
Logs, the generated audit source and a JSON report with the bridge source
SHA-256 are saved in .lake/axiom-audit/ and uploaded by CI as
lmlexplore-bridge-axiom-audit.

CI checks out the proposed PR head explicitly and records its commit SHA.
Its path filter includes the original Variation.lean and .gitattributes,
so changes to the hash-checked input also trigger verification.
Build and audit results are reported on [PR #138](https://github.com/Sumuji-zkdwn/primitive-lean/pull/138);
they apply to the recorded commit, not to an unverified future merge.

Versions: Lean 4.36.0-rc2, Mathlib
2ddf59c8f14245864e6c0ed227a2dab76b9efea2, LMLExplore
8280ba89e727bf08859d21c084dd44bca7968e1f.
Resolved transitive revisions are recorded in lake-manifest.json.
The main project retains Lean 4.30.0-rc2 and Mathlib
5450b53e5ddc75d46418fabb605edbf36bd0beb6.

LMLExplore: https://github.com/LeanMachineLearning/LMLExplore (Apache 2.0).
