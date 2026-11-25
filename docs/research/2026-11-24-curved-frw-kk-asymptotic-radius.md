# 2026-11-24 — Negative 3-curvature permits a nonflat pure-5D-vacuum circle approaching a finite positive radius

**Bounded result:** A complete local classification within the diagonal homogeneous FRW₃(k)×S¹ ansatz, and an exact **nonflat** Ricci-flat witness with positive asymptotic circle size. This is a **counterexample to extending the k=0 radius-runaway no-go to all FRW spatial curvatures**. It is NOT a demonstrated stable modulus, geodesically complete universe, particle spectrum, or novel physical solution.

## 1. Provenance / predecessor and prior literature

The source of [draft PR #263](https://github.com/Sumuji-zkdwn/primitive-lean/pull/263), corrected commit \`0478fad16ca607a767c4a30f1b3fc68fae290fe5\`, has the dedicated all-time-flat-FRW vacuum regression [45290183046](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/45290183046) and integration [45290182753](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/45290182753); **at the last retrieved checkpoint both were in progress**, not verified PASS. Initial source CI [45289791056](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/45289791056) failed at missing Lean \`noncomputable\` for a real-division definition; a single-line correction was committed. The updated PR head \`b570708c8a4d17c39124946c6697eac76056b3e7\` differed only in generated docs; exact-head runs reported \`action_required\` without jobs.

**Important pre-existing work discovered independently:** Darrell Jackson, *Re-Examination of Simple Kaluza–Klein Cosmologies* (2018), https://arxiv.org/abs/1806.09983, equations (7), (14)–(20), presents precisely this simple vacuum FRW×S¹ class, including \`b∝a'\` and \`K=72(a''/a)²\`. The older Davidson–Sonnenschein–Vozmediano (1985) and Mann–Vincent (1985) work precedes it. Bona & Bezares, *Kaluza–Klein Cosmology: the bulk metric* (2019), https://arxiv.org/abs/1904.11239, covers a wider cosmological principle and arbitrary k. **No originality/priority claim.** This PR supplies a self-contained exact reproducible finite tensor witness and a scoped local no-go refinement.

## 2. Hypotheses, tensor equations and classification

One and only one 5D smooth Lorentzian metric on an open proper-time interval I, with a(t),b(t)>0, χ periodic and a 3D constant-curvature metric γₖ (\`Ric(γₖ)=2kγₖ\`, k∈{−1,0,+1}):

\`\`\`text
ds5²=-dt²+a(t)² γ_k,ij dx^i dx^j+b(t)²dχ²,  Ric_5=0.
\`\`\`

There is **no** Λ, independent scalar/vector/flux/spinor field, brane, source, or higher curvature term. Direct Levi-Civita tensor computation yields all 25 components, with

\`\`\`text
Ric_tt = −3 a''/a − b''/b
Ric_ij = [a a''+2(a')²+2k+a a' b'/b] γ_k,ij
Ric_χχ = b b''+3 b a' b'/a
all mixed components = 0.
\`\`\`

Subtract the circle equation from time equation after multiplying by a,b to obtain \`a''b=a'b'\`, equivalently \`(a'/b)'=0\`. Substituting into the spatial equation gives

\`\`\`text
a a''+(a')²+k=0   ⇒   (a²)''=−2k.
\`\`\`

Thus on every connected positive-C² regular interval \`a'/b=C\` is a constant, and \`a²=−kt²+c₁t+c₀\`.

- If C=0 then a is constant, forcing k=0; b is affine (static or Milne-like circle).
- If C≠0, then a' never vanishes; b=B|a'| with B>0. Therefore **all** time-dependent solutions in this exact ansatz are the above quadratic family with the explicitly determined circle radius. This does not classify anisotropic, nonhomogeneous, non-product, off-diagonal, or quantum gravity.
- If b'=0 at any instant in a positive vacuum solution, the circle equation implies b''=0 at that instant, the time equation forces a''=0 and the spatial equation forces (a')²+k=0. Hence k=+1 disallows it, k=0 requires no external instantaneous expansion, and expanding k=−1 requires a'=1. Because (a³b')'=0, a moment of stationary b forces b constant throughout a connected interval; the expanding k=−1 vacuum is then the **flat Milne×S¹** geometry. A *strictly fixed circle* in an expanding nonflat vacuum remains impossible in this ansatz.

## 3. Nonflat open-universe counterexample

Take k=−1, normalized future coordinate t>0 and a parameter β>0:

\`\`\`text
γ_-1=(dx²+dy²+dz²)/z², z>0;
ds5²=−dt²+(t²+β)γ_-1+[t²/(t²+β)]dχ²;
a=√(t²+β), b=t/√(t²+β).
\`\`\`

The tensor oracle differentiates the **original five-dimensional metric** and verifies all 25 Ricci components exactly zero. It independently contracts the nonzero coordinate Riemann components to obtain

\`\`\`text
K5=R_ABCD R^ABCD = 72 β²/(t²+β)^4.
\`\`\`

For β=1 and t>0, K5>0 everywhere, so the solution is **not** merely flat Minkowski in Milne coordinates. Yet 0<b(t)<1, \`b'(t)=(t²+1)^(-3/2)>0\` and \`lim_{t→∞} b(t)=1\`. The external a(t) grows without bound. The Schwarzschild-like invariant decreases to zero at future infinity. The β=0 limit is exactly flat Milne₄×S¹ with b=1 and K5=0. A β<0 solution exists only for t>√(-β), has b>1 decreasing to 1, and a genuine past curvature blow-up as t approaches √(-β).

This is an **asymptotic constant radius, not a dynamical radion stabilizer**: the finite asymptotic constant is an arbitrary integration parameter (the scale of the circle), with no restoring potential generated by the vacuum. β>0 solution at t=0 reaches **b=0 in finite proper time**. Its Riemann scalar remains finite there, but the circle orbit degenerates and χ is periodic; a smooth, geodesically complete Lorentzian extension is *not established* and must not be assumed. No global causal or perturbative stability is proved.

## 4. Four-dimensional Einstein frame and physical audit

As a derived description of g_χχ (not an independent matter field), define

\`\`\`text
g_E4 = b[-dt²+a²γ_-1], φ=(√3/2)log b,
dτ=√b dt, α=a√b.
\`\`\`

Independent 4D Christoffel/Ricci differentiation verifies all 16 components of

\`\`\`text
Ric_E,μν=2∂_μφ∂_νφ ; □_E φ=0.
\`\`\`

The curved-FRW Friedmann constraint is \`3(H_E²−1/α²)=φ̇²\`, and the acceleration is

\`\`\`text
(1/α)d²α/dτ²=−(2/3)(dφ/dτ)²
            =−β²/[2t³(t²+β)^(3/2)] <0  (β>0,t>0).
\`\`\`

Therefore the solution is 5D vacuum and 4D decelerating, without independently added matter, but it **does not** reproduce the observed cosmological acceleration. There is one geometric U(1) from χ, not non-Abelian SU(2)×SU(3). A metric-defined scalar does not automatically provide observed chiral fermions, quantization, gauge couplings, or an equivalence-principle test. The unrelated delayed-gel/Skyrme lattice uses additional variables and is not rebranded as gravity-only.

## 5. Reproducible verification, Lean boundary, and continuation

- Independent local exact calculations (SymPy 1.14.0) have verified (i) *arbitrary* k and a(t),b(t) all 25 Ricci entries in the standard FRW radial chart, and (ii) the explicit hyperbolic model all 25 Ricci entries and full coordinate Riemann invariant K5; and (iii) the 4D Einstein-frame Ricci equations. These prototypes are exact symbolic calculations without floating point.
- Reproducible checked-in oracle \`python -B tools/check_curved_frw5_vacuum.py\` recomputes all three tests and stationary-circle examples; do not claim **this checked-in file** had CI PASS until the exact-head workflow has executed. Its CI checks installed SymPy==1.14.0 and preserves the source SHA and oracle hash.
- \`lean/Research/CurvedFRW5DVacuum.lean\` contains **12 candidate local algebraic/polynomial certificates** (two vacuum elimination identities, circle stationary at a point, k-dependent exclusions and positivity of a nonzero curvature invariant). It does **not** formalize the tensor formulas, integration, global causal conditions, topological extension, a dynamical attractor or the whole Standard Model. Pinned \`--trust=0\`, theoremwise \`#print axioms\` and allowed-axiom audit must actually succeed before a kernel PASS is reported.

**Next single finite test:** analyze the β>0 open-branch past endpoint t=0 (circle collapse with K finite) for existence or obstruction to a smooth Lorentzian compact-circle extension, separating scalar regularity from geodesic completeness and causal pathology; alternatively examine metric-only off-diagonal coupling in this same vacuum background. Keep independent PR **DRAFT**. Never auto-merge main, add matter fields silently, or announce physical unification.
