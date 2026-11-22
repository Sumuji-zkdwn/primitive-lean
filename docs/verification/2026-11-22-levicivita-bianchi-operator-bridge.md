# From the actual Levi-Civita API toward a proved second Bianchi identity

Date: 2026-11-22 (JST). Dependency: draft PR #186, target branch
chatgpt/ricci-flat-bianchi-yang-mills-20261122. No auto-merge.

## Pinned source audit

User repository: Lean 4.36.0-rc2, mathlib
2ddf59c8f14245864e6c0ed227a2dab76b9efea2.

The pinned module
Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean
constructs the Riemannian Levi-Civita connection and supplies
CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection,
with .isMetricCompatible and .torsion fields. These facts are reused in
the new proof module. In the pinned CovariantDerivative directory there
are Basic, Metric, Torsion, LeviCivita files but no existing Curvature
or second Bianchi module. This audit does not assert that no alternative
formalization exists elsewhere in the entire mathlib tree.

## Progress beyond PR #186

PR #186 proves the **contracted** second Bianchi identity conditional
on the uncontracted second Bianchi and curvature symmetries.
This module demonstrates a mathematically genuine source of the
uncontracted Bianchi identity rather than simply postulating it.

Let N_i be arbitrary finite square matrices over Q. Set

    F_ij = [N_i,N_j],
    D_k F_ij = [N_k,F_ij],

with [A,B]=AB-BA. The universal associative-algebra Jacobi identity

    [A,[B,C]] + [B,[C,A]] + [C,[A,B]]=0

implies

    D_e F_cd + D_c F_de + D_d F_ec = 0.

The Lean theorem tensor_second_bianchi packages the matrix entries in
the exact SecondBianchi format of PR #186. Theorem
contracted_for_operator_connection *reuses* the earlier contraction
proof, discharging second Bianchi via Jacobi rather than as a hypothesis.
Thus the chain reaches the contracted Bianchi identity for a class
of constructed non-flat operator connections.

The additional Yang-Mills implication is correctly conditional on
pair-exchange and covariantly constant Ricci; an arbitrary operator
connection is not guaranteed to have Riemann Levi-Civita symmetries.
The concrete 3x3 example has F_01[0,0]=1, so the construction does not
hide behind an identically flat operator connection.

## Direct use of mathlib's real geometric object

In the separate MathlibLeviCivitaBridge namespace, Lean reuses the
pinned theorem asserting the actual constructed Levi-Civita connection
has metric compatibility and torsion zero. This is a real dependency
on mathlib geometry, rather than a fake record named "Levi-Civita".

## Exact remaining boundary

The following morphism is NOT YET built and is the true next step:

    mathlib CovariantDerivative.leviCivitaConnection on TM
       |  define its Riemann curvature and its covariant derivative
       v
    coordinate operator connection + tensor-index identification
       |  Jacobi + torsion zero + metric compatibility
       v
    BianchiConnectionData for the smooth manifold
       |  PR #186
       v
    globally Ricci-flat => source-free Levi-Civita Yang-Mills

In actual manifold coordinates the N_i are differential operators,
not simply constant matrices. For nonconstant connection matrices
Gamma_i(x), curvature contains partial derivatives:
F_ij = partial_i Gamma_j - partial_j Gamma_i + [Gamma_i,Gamma_j],
and D_k F_ij also contains partial derivatives. Constant-matrix
Jacobi is an exact connection-operator model but does not by itself
prove that mathlib's Levi-Civita connection satisfies the smooth
manifold second Bianchi identity. Likewise mathlib's Riemannian API
does not automatically give pseudo-Riemannian Lorentzian connections.

No independent physical Yang-Mills bosons, Standard Model weak
interaction or other forces are reconstructed. This remains an
identity of induced gauge-like geometric curvatures.

## Reproducibility

- lean/Research/BianchiOperatorBridge.lean: Jacobi, tensor second Bianchi,
  contraction imported from #186, explicit non-flat example, and actual
  mathlib Levi-Civita metric/torsion facts.
- tools/check_bianchi_operator_bridge.py: 15 exact random matrix
  connections in dimensions 2,3,4, all cyclic Bianchi components and
  contracted identities, 3x3 non-flat example. Pure Python stdlib.
- .github/workflows/bianchi-operator-bridge.yml: pinned Lean --trust=0,
  axiom audit, independent finite oracle, exact branch head. Dependent
  draft PR must target the #186 branch, not main.

Source inspected:
https://raw.githubusercontent.com/leanprover-community/mathlib4/2ddf59c8f14245864e6c0ed227a2dab76b9efea2/Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean
