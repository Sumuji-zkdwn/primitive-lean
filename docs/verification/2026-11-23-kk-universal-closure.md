# Three KK geometry gaps: next kernel-visible bridges

Date: 2026-11-23 JST. Stacked on draft PR #219, without modifying main or earlier PR branches.

## General GH theorem
For H>0 and dA=*dH, define Theta=dpsi+A and three quaternionic candidate 2-forms Omega_i=Theta wedge dx_i-H dx_j wedge dx_k (cyclic i,j,k). The exterior derivative vanishes: dOmega_i=F wedge dx_i-dH wedge dx_j wedge dx_k=0. KKGHClosedForms.lean proves all 192 ordered coordinate exterior derivative identities for arbitrary first jets DA,p constrained by curl A=grad H; it does not specialize to a quadratic harmonic polynomial. It does not yet prove in Mathlib that a closed orthonormal self-dual triple is Levi-Civita parallel and Ricci-flat. The previous PR #219 exact SymPy verifier establishes Ricci=0 for any harmonic two-jet in canonical local gauge. Global U(1) existence also requires integrality of the periods of *dH with the chosen circle normalization; positivity and harmonicity alone are insufficient.

## General 5D-to-4D EMD
Previous PR #219 verifies 25 full off-shell reduction identities for arbitrary local normal/gauge 2-jets by SymPy. KKEMDBlockGauge.lean now proves a full 5x5 polynomial inverse relation with arbitrary four A_mu in a 4D Lorentzian orthonormal frame, not just A=0. Using q=exp(phi/sqrt(3)), the covariant metric blocks are G_mn=q*g_mn+q^-2*A_m*A_n, G_m5=q^-2*A_m, G55=q^-2. Let M=q^2 G and N=q G^-1; then M N=q^3 I. The Lean file proves the matrix product and pointwise fibre gauge invariance. It does not yet derive the Ricci-to-EMD identities for arbitrary curved g from a differentiable matrix in Lean.

## Single-centre global Hopf atlas
Previous PR #219 proves C-infinity Cartesian metric entries across X=0 and scalar rank-one eigenvalue signs. New KKHopfGlobalAlgebra.lean proves the polynomial Hopf projection on R4, its squared-radius relation, diagonal U(1) orbit invariance and action composition. KKNutQuadraticPositive.lean proves an explicit six-square Cauchy identity and strict positivity of the full spatial Taub-NUT quadratic form for alpha>=0 and nonzero tangent vector. Algebraic North/South fibre transitions and 4*pi*k period are already in KKNutPatching. The smooth quotient S3/U(1)≈S2, complete smooth bundle atlas and global metric pullback/diffeomorphism equivalence remain external to Lean.

## Verification and boundary
Dedicated CI compiles the new modules with repo-pinned Lean --trust=0, audits every theorem's axioms and executes an independent SymPy checker of 192 GH closure components, 25 KK inverse entries, Hopf orbit invariance and the positive-form six-square identity. Until the CI succeeds, new declarations are not certified. These are genuine intermediate mathematical facts; do not label them the three complete Lean theorems.

Original known constructions: Gibbons--Hawking metrics, Einstein-frame KK reduction, standard Hopf fibration. No novel physical forces are claimed. Draft only, no merge.
