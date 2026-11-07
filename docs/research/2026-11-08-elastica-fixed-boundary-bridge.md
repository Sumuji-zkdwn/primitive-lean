# Fixed-boundary Elastica / operator-quotient bridge

## Scope and pinned sources

This is an additive follow-up to [PR #99](https://github.com/Sumuji-zkdwn/primitive-lean/pull/99)
at `abc94a7d313efc194fe43a6bfc1ed955fa36f17b` and
[PR #100](https://github.com/Sumuji-zkdwn/primitive-lean/pull/100)
at `a721c47b6cfa18ef101fd5dc563881c3c9654af7`.
The original theorem statements and proof bodies are unchanged.

The operator-word and refinement fragments and the initial `Elastica.Geometry`
source are checked byte-for-byte against #99. The #100 curvature bridge is
checked against its specified commit. The verification script assembles their
existing declarations in a temporary module; it does not maintain a second
repository copy of the generic quotient theory. The toolchain is
Lean `v4.30.0-rc2`, with mathlib at
`5450b53e5ddc75d46418fabb605edbf36bd0beb6` and the other dependency revisions
from `lean/lake-manifest.json`.

## Definitions and checked theorems

Let

```text
f(s) = (1/2) sin(2πs) − (1/4) sin(4πs)
θ₀(s) = f(s), θ₁(s) = −f(s), θ₂(s) = f(s + 1/2).
```

Each θ is a global real-valued tangent-angle lift. Coordinates are the
original `Elastica.xCoord` and `Elastica.yCoord`, initialized at `(0,0)`
and read at `s=1`. The observer reads `Elastica.curvature θ 0`.

| Statement | Lean declarations |
| --- | --- |
| All angle functions are smooth and pairwise distinct | `angle_smooth`, `angle_injective` |
| Reconstructed curves have squared speed 1 | `unit_speed`, using `Elastica.unit_speed_squared` |
| Both endpoint positions and both endpoint angles agree | `angle_initial`, `angle_final`, `common_x_endpoint`, `common_y_endpoint`, `shared_boundary` |
| Initial curvatures are 0, 0, −2π | `curvature_zero`, `curvature_one`, `curvature_two` |
| All three integrals of squared curvature equal π² | `FixedBoundaryExactEnergy.quadratic_bending_value` |
| The old identity action and new 1→2 action split the predictive quotient | `fixed_boundary_quotient_splits` |
| The same split holds directly on the subtype of represented angle functions | `represented_curve_split` |
| Smoothness, speed, shared boundary, exact bending integral, and the split hold together | `FixedBoundaryExactEnergy.exact_represented_realization` |

Unqualified names in the table are in the `FixedBoundaryWitness` namespace.
The represented subtype and `angle_injective` ensure that the positive
example does not rely on two labels denoting the same angle function. The
actions on that subtype are obtained by transporting the finite actions along
the equivalence between `Fin 3` and the image of `angle`.

The quotient theorem invokes the existing
`LinearInputOperatorRefinement.strict_refinement_splits_quotient`.
The abstract equivalence and quotient maps in
`ElasticaUnifiedOperatorAdapter` compare the actual #99 operator theory with
the actual #100 definitions for identical observers and transitions. In
particular, `curvature_as_old_example` identifies #100's real curvature
readout with the real embedding of the earlier finite `exampleK`; the two
action definitions also coincide. The generic theorem is not reintroduced.

## Proof dependencies and independent checks

`ElasticaDependencyAudit.lean` inspects constants in Lean's accepted theorem
bodies. It verifies direct edges and restricted theorem-body paths including:

```text
#99 elastica_quotient_splits
  → old_indistinguishable → observer_one → Elastica.xCoord_const
#100 curve_split
  → fresh_separates → K_two → Elastica.curvature_affine
exact_represented_realization
  → represented_unit_speed → unit_speed → Elastica.unit_speed_squared
exact_represented_realization
  → represented_curve_split → strict_refinement_splits_quotient
```

These are explicit paths through theorem proof bodies, not a claim that a
separately computed complete project dependency graph was regenerated.
`tools/verify_elastica_fixed_boundary.py` compiles with `--trust=0`,
checks for proof placeholders, and checks every newly declared theorem,
definition and abbreviation for axioms beyond `propext`, `Classical.choice`,
and `Quot.sound`.

The independent standard-library Python tests enumerate the finite transition
monoid to closure, verify the old/new partitions and inert extension, and
numerically integrate coordinates and curvature squared with composite Simpson
quadrature. They also calculate the Fourier coefficients and curvature/energy
coefficients exactly using rational arithmetic. Numerical integration is a
cross-check; the exact boundary and π² statements are Lean theorems.

On 2026-11-08 (JST), the additive working tree based on the pinned #100
commit passed the command below locally: five independent Python tests,
the original and new Lean modules compiled with `--trust=0`, the specified
proof-term paths were found, and all 76 new declarations passed the permitted
axiom check. The pinned Lean, mathlib, and manifest dependency revisions were
checked. This local result is separate from any later GitHub Actions run.

## Boundary of the claim

This is a finite deterministic transition system on actual, smooth, unit-speed
angle functions with equal fixed endpoint positions and angles. It is not a
construction of a continuous path in the fixed-boundary configuration space,
a middle replacement that keeps an exterior neighborhood unchanged, an
Euler–Lagrange stationary family, or a physical dynamical law.
The new transition changes curvature at the initial point; therefore it cannot
be an operation that keeps an entire initial neighborhood unchanged.
The equal quadratic bending integral is a separate specialization and does not
assert equality for arbitrary curvature-energy densities.

## Reproduction and CI scope

Fetch the two pinned commit objects and obtain the pinned mathlib cache, then:

```sh
git fetch origin abc94a7d313efc194fe43a6bfc1ed955fa36f17b
git fetch origin a721c47b6cfa18ef101fd5dc563881c3c9654af7
cd lean && lake exe cache get && cd ..
python -X utf8 tools/verify.py --elastica-boundary-only
```

The new dedicated workflow invokes this unified entry point for the relevant
PR and main-push changes. The existing `--integration-only` mode is unchanged
and does not by itself discover these independent `.lean` modules.
CI success must be read from a run for the exact new head; the existence of
the workflow alone is not a successful CI result.
