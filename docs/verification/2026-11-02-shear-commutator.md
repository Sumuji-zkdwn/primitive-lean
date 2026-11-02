# 2026-11-02: gradient-generated shear commutator

## Source and logical status

This is an additive theorem supplement on the research branch
codex/primitive-history-derivation-20261029 of
Sumuji-zkdwn/primitive-lean. It does not modify the original
Elastica or polynomial-energy source.

**Existing formalized input**:
- LinearInputDesign.E (the original primitive energy)
- LinearInputVariablePairs.energy_eq_primitive (the exact bridge)
- linear_input/lean_check/VariablePairObservations.inc
- LinearInputVariablePairs.energy
- LinearInputVariablePairs.hasDerivAt_energy_x
- LinearInputVariablePairs.hasDerivAt_signed_input
- LinearInputVariablePairs.gradXu_formula

The source potential is also an exact slice of the ORIGINAL Design.E at
lam=0, r=k-2, y=0, and input=-u; the new Lean theorems
source_is_original_energy and original_gradient_formula prove the
energy and both partial-derivative identities. With this explicit
chosen sign s=+1, the potential is

    energy k 0 0 0 x 0 (-u) = (k/2)*x^2 + u*x.

Its actual paired derivative is G_k(x,u)=(kx+u,x).
Define P(x,u)=(u,x). The two shears are not separately axiomatized:

    A_k = G_k ∘ P = (x+ku,u)
    B_k = P ∘ G_k = (x,u+kx).

The placement of P, the sign choice, and the alternating word are
additional constructions chosen for this investigation. They are not
forced by the mere existence of the original variational energy.

## Derived algebra

With undoA = A_a^-1 and undoB = B_b^-1, the actual
operation order A, B, undo A, undo B acts as

    C_{a,b} = undoB_b ∘ undoA_a ∘ B_b ∘ A_a

and has explicit matrix

    [ 1-ab       -a^2 b          ]
    [ ab^2        1+ab+a^2 b^2   ].

det C = 1, tr C = 2+(ab)^2. When real a and b are
both nonzero, tr C > 2, hence this real 2x2 SL(2) map is
hyperbolic. With a=b=1,

    C(x,u)=(-u,x+3u)
    (1,0) -> (0,1) -> (-1,3) -> (-3,8) -> (-8,21)

and its characteristic polynomial is t^2-3t+1, with
expanding root (3+sqrt(5))/2 = ((1+sqrt(5))/2)^2.

## Exact lower bound without eigendecomposition

The cone u>0, -u/2 <= x <= 0 is forward invariant.
For every state in this cone, the next vertical coordinate obeys

    u' = x+3u >= (5/2)u.

As (0,1) is the state after the first loop from (1,0),
the source explicitly proves, for each natural n,

    ((C_1,1)^n (0,1)).2 >= (5/2)^n.

This is a rigorous exponential lower bound for the stated orbit,
not a claim that every real initial state grows: one stable real
eigendirection contracts. There is no physical free energy claim.

## Artifacts and verification

- Lean supplement: linear_input/lean_check/ShearCommutator.inc.
- Combined registration and all-declaration audit:
  tools/verify_main_result.py, tools/verify.py.
- Independent exact-arithmetic test: tools/check_shear_commutator.py.
- Entry point: python -B -X utf8 tools/verify.py --proof-only.
- Separate arithmetic entry: python -B -X utf8 tools/check_shear_commutator.py.
- GitHub Actions: .github/workflows/primitive-lean-ci.yml.

The written Lean terms are intended proof obligations. Actual
success/failure must be established by the specific pinned
Lean/mathlib CI run against the final head SHA; writing the source
alone does not certify that it compiles.
