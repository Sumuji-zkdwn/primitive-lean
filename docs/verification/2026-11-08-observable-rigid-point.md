# Observable rigid point from primitive-lean F0 (2026-11-08)

## Definition and precise mathematical claim

This is a formal *observable common fixed point*, not the claim that an
infinitely rigid physical state, thermodynamic critical point, or seismogenic
phase boundary exists.

Use the retained \`LinearInputF0.Idempotent\` and
\`LinearInputF0.fixed_iff_in_range\` from
\`linear_input/lean_check/F0Retractions.inc\`.

For an idempotent observer \`K : α → α\` and updates \`M,C : α → α\`, put
\`U = K ∘ M\` and \`V = K ∘ C\`. If \`U²=U\`, \`V²=V\`,
and \`UV=VU\`, then, for every \`x\`,

\`\`\`text
q = U(V(x))
K(q) = q
U(q) = q
V(q) = q
q in range(K)
\`\`\`

The exact last inclusion invokes the *existing* F0 theorem.
The raw micro-updates \`M,C\` need not commute, and a future enlarged observer
can reveal their history. Without effective commutation, two idempotents can
have disjoint fixed-point sets: the constant-false and constant-true maps on
\`Bool\` are a two-state countermodel.

## Nontrivial four-state witness

Let \`x=(a,b) ∈ Bool × Bool\`, \`K(a,b)=(a,0)\`,
\`M(a,b)=(0,b)\`, \`C(a,b)=(a,a)\`.

From \`x=(1,0)\`,
\`M(C(x))=(0,1)\` and \`C(M(x))=(0,0)\`, but both project to \`(0,0)\`.
Thus the microscopic commutator is visible with a sufficiently strong observer,
yet the projected \`U,V\` are commuting idempotents. The observational
common fixed point is \`(0,0)\`.

## Independence and verification status

\`tests/test_observable_rigid_point.py\` exhaustively tests all commuting
ordered pairs of idempotents for 2, 3, and 4 states: respectively 7, 58,
and 601 pairs (from 3, 10, and 41 idempotents), with every initial state.
It also covers incompatible constants and the four-state hidden-order model.

Lean: \`LinearInputRigidPoint.common_fixed_of_commuting\`,
\`observed_rigid_exists\`, \`observed_rigid_in_Krange\`,
\`no_common_without_commutation\`, and the concrete finite model are
in the additive registered proof \`ObservableRigidPoint.inc\`.
Successful Lean \`--trust=0\` compilation is **not claimed** until this
exact PR head is checked by CI.

## Boundaries

This extension imports no melting kinetics, crystallization law,
force balance, temperature, transport PDE, or actual physical material.
It does not claim the actual Elastica Euler–Lagrange dynamics generate
\`M,C\`, or that the common fixed state is dynamically stable. The
curvature-based two-well extension in PR #91, and the context-separating
join example in PR #87, are adjacent research lines, not proof dependencies.
The further bridge requires explicit constitutive and measurement assumptions.
