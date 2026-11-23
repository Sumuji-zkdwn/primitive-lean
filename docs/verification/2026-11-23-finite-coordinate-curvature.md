# Reusable finite-frame curvature layer — scope and verification

Date: 2026-11-23 JST. Independent Draft PR based on main, deliberately
not stacked on the long GH/EMD/Hopf Draft PR chain. No main changes.

## Goal

Isolate the one step that several earlier project modules duplicated:
construct the **curvature and Ricci of a finite-frame connection** from
its coefficient matrix Gamma and its first derivative jet dGamma.

On a finite frame with base indices i,j and fibre indices a,b define

    R^a_{b i j} =
       dGamma[i,j,a,b] - dGamma[j,i,a,b]
       + sum_c (Gamma[i,a,c]*Gamma[j,c,b]
              - Gamma[j,a,c]*Gamma[i,c,b]).

This is the coordinate curvature of a connection, with derivative-first
index convention. No Riemannian metric, Lorentz signature, or GH/EMD
specific expression is required. For a tangent connection, define

    Ric_{j,l} := sum_a R^a_{l a j}.

The generic Lean core proves skew-symmetry R_ij=-R_ji, diagonal
vanishing, the flat-zero-connection case, equality for constant
connections with the matrix commutator, and the matrix Jacobi
identity. The latter is the algebraic part of the Bianchi story,
not a differential Bianchi theorem.

## Explicit nonflat validation

A separate module has exact rational Γ and ∂Γ point values for the
Riemannian metric g=dx²+(1+x²)² dy² at x=1. The independent SymPy
oracle derives the inverse metric, the complete Levi-Civita coefficient
table and all first derivatives from that metric. It checks the
entire curvature and Ricci tensor:

    Gamma^1_(01) = Gamma^1_(10) = 1, Gamma^0_(11) = -4,
    partial_x Gamma^0_(11) = -8.
    Ric(1) = diag(-1,-4) = -g(1),  R^0_(1 0 1) = -4.

This avoids a false confidence test where every curvature entry
would vanish by definition. It also checks the Jacobi identity
for 3x3 matrices with arbitrary symbolic entries.

## The formal guarantee boundary

The Lean generic definitions and theorems treat **the first connection
derivative jet as data**. The witness Lean theorem checks the
curvature contraction for a specific supplied rational jet. It does
not prove the actual metric -> Levi-Civita -> coefficient jet
calculation in the Lean kernel. SymPy does independently verify that
calculation for the explicit curved test metric.

Mathlib already has abstract manifold covariant derivatives and a
Riemannian Levi-Civita construction in
Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative.
This new file does not claim to replace or connect directly to that
API, and is *not* yet a general metric-to-Ricci formal theorem.

Next focused shared task:
1. Replace the free dGamma values by a commuting derivation family
   D_i acting on a commutative algebra of smooth coefficients.
2. Prove [nabla_i,nabla_j]s^a = sum_b R^a_(b i j)s^b
   using Leibniz and commuting partials.
3. Connect chartwise instances to Mathlib CovariantDerivative,
   and formalize geometric curvature/Ricci in a reusable general API.
4. Apply that shared theorem in GH and 5D->4D EMD work, including
   the pseudo-Riemannian normalization where required.

No claim of new physical equations or of a GH/EMD theorem in Mathlib.

## CI

The dedicated workflow pins the repository toolchain and Mathlib,
compiles under Lean --trust=0, audits each theorem using #print axioms,
runs exact SymPy 1.14.0, and saves logs and source SHA256. A successful
CI is required before calling the core kernel-verified.

Keep Draft. No automatic merge or edits to existing GH/EMD/Hopf PRs.


## Follow-on: rank-one curvature from commuting derivations

The new FiniteConnectionDerivation.lean module goes beyond independent
derivative tables in a controlled, reusable setting. It defines a
structure of commuting additive scalar derivations with a genuine
Leibniz law, and the associated rank-one covariant derivative
nabla_i s = D_i s + Gamma_i s. Theorems proposed for kernel checking:

    nabla_i(f s) = (D_i f)s + f(nabla_i s)
    (nabla_i nabla_j - nabla_j nabla_i)s
       = (D_i Gamma_j-D_j Gamma_i)s

A third theorem identifies that coefficient with the general finite
curvature formula when the fibre has rank 1. Unlike the original jet
file, dGamma is **actually calculated using derivations**. The
structure's hypotheses are not proven for every arbitrary smooth
manifold; that requires a coordinate derivative instance.

The higher-rank operator commutator and a fully geometric
Mathlib CovariantDerivative-to-curvature theorem are still open.
This is not GH/EMD Ricci flatness nor KK reduction.

The successful first dedicated CI 45139993911 covered 11 theorems
(the generic finite-frame core and warped-metric witness) and exact
independent SymPy tests. The additional derivation module is a
subsequent source change and must be audited by the next exact-head CI.
