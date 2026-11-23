# 2026-11-23 — Smooth finite-energy wall can be bypassed on the five-site S³ simplex

**Status:** one exact finite counterexample with independent local SymPy 1.14.0 algebra and universal inequality checks. Candidate Lean algebraic lemmas and a dedicated pinned trust-zero/axiom-oracle CI are supplied; **do not claim new-head Lean PASS until checking the run**. This is a manually designed SU(2)-valued lattice effective theory, NOT pure higher-dimensional gravity.

## 1. Predecessor / exact-head audit

In [#207](https://github.com/Sumuji-zkdwn/primitive-lean/pull/207), geometric admissibility on the five-tetrahedron boundary ∂Δ⁴⊂R⁴ makes the degree of normalized affine interpolation well defined. Direct deformation crosses the inadmissible face at t=1/6. Its earlier source commit `25564d0fb7104848fc10ac7930b06f212a313aab` was confirmed by [dedicated run 45083264000](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/45083264000): Lean --trust=0 PASS, 12 theorem-by-theorem axiom audits PASS, SymPy PASS. Its then-current head `2b661a05b79cb8901bd38d707b134d3517d5bf26` differs only in three docs/dependency/generated files; latest-head workflows returned `action_required` with no jobs, not a Lean compilation failure. This PR is a fresh independent branch from main, not an edit to #207.

**Next finite question:** can one replace a hard excluded geometric wall by an everywhere smooth, finite energy that creates an absolute topological sector barrier? Distinguish a large barrier on one chosen path from the global minimax barrier over *all* paths.

## 2. Model, criterion and exact formulas

Take five site values qᵢ∈S³⊂R⁴ with initial values v₀=e₀, v₁=e₁, v₂=e₂, v₃=e₃, v₄=−(e₀+e₁+e₂+e₃)/2 and uniform final values qᵢ=e₀. Let r=√(21/26), 0<r<9/10, and a fixed “selected barycentric soft witness”

```text
z(q) = q1 + q2 + q3 + 2r q4,
S(q) = ||z(q)||²,
V(q) = 1 / (1/100 + S(q)),
E(q) = (1/2) Σ_{0≤i<j≤4} ||qi−qj||² + V(q).
```

The potential V is C∞ (indeed real analytic) and **bounded 0<V≤100 on the entire compact configuration space (S³)^5**. It is *chosen by hand* to suppress one particular geometric zero; it is **not** a universal, permutation/gauge-invariant physical topological density. On K₅ there are 10 bonds, each contributing at most 2 to E₂; hence 0≤E₂≤20 and 0<E≤120 globally.

Direct path from #207: q₀=e₀ and qᵢ(t)=wᵢ(t)/||wᵢ(t)|| for i=1..4, where wᵢ(t)=(1−t)vᵢ+t e₀. All norms are positive for 0≤t≤1. At `t*=1/6`, `w1+w2+w3+2w4=0`; ||w1||=||w2||=||w3|| and `2r=2||w4||/||w1||`. Thus **z(q(t*))=0 and V(q(t*))=100**. The direct path's total energy reaches at least 100. Its initial E₂ is 12 and total initial E<14; the final E₂ is 0 and total E<1.

## 3. Exact alternative path with maximum E<70

Instead of moving sites 1..4 together, move them *sequentially* to e₀ along their normalized affine unit-S³ arcs, leaving all already moved sites at e₀ and all not-yet-moved sites at their initial values. Four continuous segments concatenate to the same final vacuum. Every intermediate state remains in (S³)^5, with strictly positive normalization denominators.

- **Segment 1:** move q₁, with q₂=e₂, q₃=e₃, q₄=v₄. The fourth Cartesian component of z is `1−r`, so `S≥(1−r)²`.
- **Segment 2:** move q₂ after q₁=e₀, while q₃=e₃, q₄=v₄. The same component gives `S≥(1−r)²`.
- **Segment 3:** move q₃ after q₁=q₂=e₀; q₄=v₄. The first Cartesian component of z is `2+q3[0]−r≥2−r>1−r` since q3[0]≥0.
- **Segment 4:** with q₁=q₂=q₃=e₀, move q₄ from v₄ to e₀. Since ||q₄||=1, the triangle inequality yields `||z||≥3−2r>1−r`.

Exact `r<9/10` gives `(1−r)²>1/100`. Therefore on **every segment**,
```text
S>1/100,
V<1/(1/100+1/100)=50,
E=E₂+V<20+50=70.
```

This is an **exact uniform upper bound for a continuous path** connecting the degree-nonzero initial site configuration and the degree-zero vacuum in the unconstrained field space. There is no energy barrier of 70 or greater between them for this particular soft potential, despite the 100+ spike on the direct path. The globally minimized barrier may be even lower.

**Where did the true topological wall go?** It was NOT eliminated. During the **first segment** at `s=1/2` the unnormalized face opposite v₀ has a strictly positive convex-zero witness:

```text
2 w1 + w2 + w3 + 2 w4 = 0
positive weights (2,1,1,2)/6.
```

After positive site rescaling, this is still a convex-hull zero for unit vertex values, so the geometric normalized affine interpolation becomes undefined there. But the chosen smooth z is *nonzero* at this alternative wall; exactly,
```text
S = 2(1/√2−r)² + 2(1−r)² > 1/100;
E₂ = 23/2.
```

Thus the deliberately targeted soft potential fails to penalize a different barycentric crossing even of the **same** tetrahedral facet. This does not contradict the hard-admissibility theorem of #207: the bypass is not a homotopy within the hard-admissible subset.

## 4. Stronger general obstruction / verification scope

**General mathematical argument (external, not kernel formalized):** On any path-connected configuration space X, if E:X→R is a finite continuous energy, any continuous path γ:[0,1]→X has a compact image and `max E∘γ<∞`. Hence **no exact infinite energy separation follows** from such an energy, although finite-energy sublevel components can be disconnected and metastable. In this finite model X=(S³)^5 is path-connected; in fact compact, so every continuous finite E is globally bounded. A true topological sector here needs an excluded singular locus, a singular/infinite penalty, a specified interpolation rule restricting admissibility, or a nontrivial continuum-limit construction. None follows automatically from a smooth finite polynomial/rational elastic energy.

**Independent reproducibility:** `python -B tools/check_finite_soft_wall_bypass.py`, SymPy==1.14.0, checks exact r², five site norms, initial/final energies, the direct z=0 certificate, all four stage endpoint/coordinate formulas, positive margins, the alternate strictly-positive face barycentric zero, E₂=23/2 at that crossing, and the strict **<70 vs ≥100** inequality. Exact finite identities + elementary analytic inequalities; no floating-point simulation.

**Lean scope:** `lean/Research/FiniteSoftWallBypass.lean` contains 15 small candidate algebraic inequality/barycentric lemmas, with a workflow for pinned Lean --trust=0, theorem-by-theorem `#print axioms`, explicit allowed standard axioms, and independent SymPy. This Lean file does **not** certify homotopy degree, all configurations, geodesic paths, or dynamics. Exact-head CI must be checked.

**Physics audit:** q_i are independent SU(2) site fields not derived from a higher-dimensional Einstein metric. The energy explicitly selects vertices and an irrational weight; it is not invariant under full physical Lorentz transformations or lattice relabellings, and no stress-energy conservation or general covariant equations are derived. This finite counterexample neither creates nor rules out physical Skyrmions. No fermions, quantization, gravity-only matter, or Standard Model reconstruction is claimed.

## 5. Established precursors and next finite experiment

- B. Berg and M. Lüscher (1981), *Definition and statistical distributions of a topological number in the lattice O(3) σ-model*, https://doi.org/10.1016/0550-3213(81)90568-X — geometric lattice topological charge in 2D; not the same 3-sphere finite witness.
- M. Lüscher (1982), *Topology of Lattice Gauge Fields*, *Comm. Math. Phys.* **85**, 39–48, https://doi.org/10.1007/BF02029132 — topological sectors under a small-action/admissibility restriction. This work and elementary compactness/degree theorems are **prior mathematical context**, not novel claims of this PR.

**Next one bounded test:** replace the artificially chosen single-combination potential by a symmetric `min_{λ∈Δ³} ||Σλq||` or smooth-averaged version that detects *all* convex-zero facets, then quantify its finite barrier with ε>0 versus its singular ε→0 limit; independently ask whether any corresponding term can be derived from higher-dimensional **Ricci-flat metric data without adding an independent field**. Never infer a physical stable particle solely from static lattice barriers.

Keep **DRAFT**, no automatic main merge, no release or paid service.
