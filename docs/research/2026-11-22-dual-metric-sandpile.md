# Two distance structures and observer-dependent sandpile patterns

Date: 2026-11-22 (JST).
Status: finite Lean candidates; independent Python tests passed locally. Lean CI and axiom audit require exact-head verification.

## Main question

Can a common site set have one metric for an observer's apparent distances and a different metric for local redistribution while remaining a coherent mathematical structure? Yes. However, changing metric values alone does not necessarily change toppling dynamics.

## Smooth continuous witness (mathematical argument, not Lean-proved)

On M = R², take the Euclidean outer metric and a smooth inner Riemannian metric

    g_inner = λ(x,y)² (dx²+dy²),    λ(r) = 1 + 99/(1+r²),  r²=x²+y².

Here λ is strictly positive and C-infinity; it lies between 1 and 100, so length distances obey

    d_outer(p,q) ≤ d_inner(p,q) ≤ 100 d_outer(p,q).

For radial motion from (0,0) to (1,0), the intrinsic inner distance is

    ∫_0¹ [1+99/(1+r²)] dr = 1 + 99π/4 ≈ 78.75,

while the outer distance is 1. The radial path is minimizing because for any piecewise C¹ path γ the radial coordinate r(t)=|γ(t)| satisfies |r'(t)|≤|γ'(t)| almost everywhere, yielding the same lower bound on length. Thus both metrics are smooth, bi-Lipschitz equivalent, and topologically compatible; intrinsic size can nonetheless differ drastically. This does not require separate disconnected spatial universes.

## Finite Lean witness

V = Fin 3, symmetric finite metrics specified by pairwise distances:

| d | d(0,1) | d(1,2) | d(0,2) |
|---|---:|---:|---:|
| outer | 1 | 1 | 2 |
| inner | 1 | 3 | 4 |
| innerVariant | 1 | 2 | 3 |

Each is a metric on precisely the same points (finite metrics do not formalize differentiable smoothness). The Lean module proves metric axioms and d_outer ≤ d_inner ≤ 3d_outer.

Turn each metric into a finite graph with edge(i,j)=1 iff i≠j and d(i,j)≤1, and add one outgoing sink edge at each vertex. Threshold(i)=1+sum(edge(i,j)). A legal firing at vertex i removes threshold(i) chips there, adds edge(i,j) chips at each other vertex j, and dissipates one to the sink. Legal firings preserve nonnegativity, and strictly reduce total non-sink mass by one. Hence all legal firing sequences terminate.

- Outer graph is 0--1--2 with thresholds (2,3,2).
- Inner graph is 0--1 with vertex 2 internally isolated, thresholds (2,2,1).
- From (0,1,0), both are already stable.
- From (0,2,0), outer remains stable, while inner fires once to (1,0,0), also stable.

A theorem proves that *any two distance functions inducing the same threshold graph* have the same firing operation on all configurations. Inner and innerVariant give a concrete pair of different metrics that the chosen toppling operations cannot distinguish. This is a strong separation of geometry and operational observation.

The finite Python oracle performed 4 tests, including all 52 integer metric triples with pair distances 1..4 satisfying triangle inequalities and all 64 initial chip configurations with coordinates 0..3. It compared two deterministic legal firing priorities: 3,328 matched stable outcomes. For inner/variant, all 125 configurations with coordinates 0..4 gave identical stable outcomes.

## Scope limitations

These results do not show causal equivalence of physical spacetime, nonuniqueness of actual histories, or a smooth gluing from a metric graph to a continuous manifold. No general Abelian sandpile order independence is claimed as a newly Lean-proved theorem: only the equality of one-step firing maps is generic Lean content, and bounded order-independence is independently checked by Python. Because graphs use a hard adjacency threshold, small changes to metric lengths across that threshold may alter dynamics discontinuously.

## Source / verifier

- lean/Research/DualMetricSandpile.lean: metric axioms, metric comparisons, graph threshold, edge/transition invariance, explicit one/two-chip witness.
- tests/test_dual_metric_sandpile.py: finite exact arithmetic oracle and bounded census.
- .github/workflows/dual-metric-sandpile.yml: pinned exact-head Lean compile, axiom audit, and Python oracle.

## Next theorem

If observers relabel sites by a bijective isometry of their thresholded graphs, then legal firing, stabilization, and final observed patterns commute with this relabeling. This is the natural finite analogue of covariance; it must not be confused with Einstein equivalence principle.