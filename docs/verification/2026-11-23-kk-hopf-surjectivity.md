# Next Hopf fibration bridge: algebraic surjectivity onto S²

2026-11-23 JST. Stacked Draft PR on #225, itself based on #222. Do not merge into main. Parent PR #225 proved Hopf fibres are precisely free U(1) orbits, but did not prove every point of S² lies in the image.

For any (u,v,w) with u²+v²+w²=1 and w≠-1, choose:

    d = sqrt(2(1+w)) > 0
    X = ((1+w)/d, 0, u/d, v/d) ∈ R⁴.

Then |X|²=1, hopfX(X)=u, hopfY(X)=v and hopfZ(X)=w. The missing south pole (0,0,-1) has preimage X=(0,0,1,0). These are explicit chart data, with the square root justified by 1+w>0. The independent SymPy script checks the exact numerator identities.

Lean theorem target: KKHopfSurjective.hopf_surjective_on_unit_spheres. Combined with the parent orbit-completeness theorem, this yields a set-theoretic identification of S³/U(1) with S²; a Lean quotient equivalence is a separate next step.

**Boundary:** Does not prove smoothness of a principal-bundle local trivialization, the quotient manifold topology, S³/U(1) ≅ S² as a diffeomorphism, transition winding / first Chern class, or the general GH/EMD smooth curvature reductions.

The dedicated workflow checks repository-pinned Lean --trust=0, all new theorem axioms and the independent SymPy oracle. Before CI success these Lean declarations are only proof candidates.


## Kernel-checked quotient and two-chart results

- [run 45116469473](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/45116469473) passed the full north-chart S³ → S² surjectivity proof, pinned Lean `--trust=0`, individual axiom audit and independent SymPy.
- [run 45117052598](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/45117052598) passed the setoid/quotient module. In `KKHopfQuotient`, the setoid equating Hopf projections is proved equal to the actual unit-circle orbit relation; `descent_bijective` then proves a bijection from the quotient to S². `orbitEquivS2` is a Lean `Equiv`, *not* a `Homeomorph`.
- [run 45117231780](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/45117231780) passed the south stereographic section, existence of a unit-phase transition on the overlap, and uniqueness of the phase acting on a unit S³ vector. These are pointwise, not yet analytic smoothness/continuity or a winding-number proof.

The local section formulas are

    north: ((1+w),0,u,v)/sqrt(2(1+w)),   for w>-1;
    south: (u,-v,(1-w),0)/sqrt(2(1-w)),   for w<1.

The two local sections cover S². Their overlapping images differ by a unique
diagonal unit complex phase. No Mathlib quotient topology theorem, smooth
principal bundle, transition degree, or diffeomorphism has yet been proved.

The orbit-equivalence result is genuinely set-theoretic, even though the parent
geometry naturally admits a smooth and topological quotient. This distinction
is preserved in all PR claims.
