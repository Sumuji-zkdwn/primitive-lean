# 2026-11-24 — Exact time-dependent 5D vacuum Kasner circle: expansion without matter, but unavoidable radion runaway

**One bounded independent test, pure metric only.** Source and CI claims are deliberately separate: independent local SymPy 1.14.0 algebra PASS (all 25 vacuum Ricci entries, full 5D Kretschmann, 4D Einstein-frame Ricci/scalar equations, all power-law branches). Ten *candidate* Lean polynomial classification theorems are included, but do not claim kernel PASS until checking the exact source-head workflow. The solution and 4D Kaluza–Klein reduction are known, not novel field equations.

## Previous checkpoint / CI lineage

Prior noncompact internal gravity draft [#260](https://github.com/Sumuji-zkdwn/primitive-lean/pull/260), source HEAD f251f656b04f8991c468f6df234c94a0df095f4e: dedicated [45278639134](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/45278639134) and integration [45278639027](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/45278639027) both **SUCCESS**. It proves using an external published global rigidity theorem that a smooth complete noncompact Ricci-flat internal metric and exactly Minkowski4 external space with a positive block-diagonal warp cannot supply finite ordinary four-dimensional kinetic coefficients. Its exception example is incomplete. This does **not** rule out time-dependent external metrics.

Other checked draft source HEADs as of this research cycle: #176 ba1dc78f9be0ca3867fcaeb5b51dde01687c3ff2 (dedicated 44952037270, 44952037252); #177 8a84ab5a623150c1dc2df6f8614e4b5f0df7d485 (44953750468); #178 5ce3ddc293417ffea43c79b99b16e36ff1594186 (44954103336); #179 cb0549a92dc2d7297093196788d6936f21418098 (44955089236); #183 8a6ffd4b9d91a5e3f41238da841b2a64b70a846c (integration 44958061416). These source-head workflow results remain **action_required** (not compiler failures) rather than verified kernel runs. Do not apply speculative fixes to these drafts. Independent SU(2) gel/grid branches remain conceptually separate from metric-only gravity.

## Precise model and pass/fail conditions

Let M=(0,∞)×R³×S¹, y≡y+2π; all spatial xᵢ noncompact, internal circle compact for each t>0, and use only the five-dimensional Einstein–Hilbert metric with zero cosmological constant, no Yang–Mills, spinor, flux, brane, or external matter field. Impose homogeneous isotropic three-space and a time-dependent compact circle:

\`\`\`text
ds5² = -dt² + t^(2p)(dx₁²+dx₂²+dx₃²) + t^(2q) dy² .
\`\`\`

The physical t domain is t>0; all metric coefficients are smooth there, and the circle has proper radius b(t)=t^q (up to a fixed coordinate radius). The external spacetime is **not** Minkowski unless p=0, and the reduction is **time-dependent**, so the compact static no-go hypotheses do not apply.

Required: exact Ric5=0 in all components; classify real (p,q) including flat/static edge cases rather than assuming sum pᵢ=1; compute Kretschmann and proper 4D Einstein-frame field equations; distinguish artificial matter interpretation; record failures against cosmological acceleration, internal-radius stabilization, non-Abelian gauge groups, particle spectrum and quantum physics.

## 5D Ricci, exact classification, singularity

Direct Christoffel differentiation gives diagonal Ricci components:

\`\`\`text
Ric_tt = [3p(1-p)+q(1-q)]/t²
Ric_xixi = p(3p+q-1) t^(2p-2), i=1,2,3
Ric_yy = q(3p+q-1) t^(2q-2)
all mixed Ricci components = 0.
\`\`\`

Exactly solving the three polynomial residuals over real p,q yields **all** branches:

\`\`\`text
(p,q)=(0,0): completely static Minkowski5.
(p,q)=(0,1): locally flat Milne-like expanding circle (periodicity prevents naive smooth completion at t=0).
(p,q)=(1/2,-1/2): the unique expanding external three-space in this power-law ansatz.
\`\`\`

The unique expanding solution is

\`\`\`text
ds5² = -dt² + t (dx₁²+dx₂²+dx₃²) + t^-1 dy².
\`\`\`

SymPy computes **all 25 entries of Ric5 to be zero**. Independent direct 5D coordinate Riemann contraction and the orthonormal Kasner exponent formula both give **R_{ABCD}R^{ABCD}=9/(2t⁴)**. Consequently t→0 is a genuine curvature singularity reached in finite proper time by comoving observers; the region is not past-complete. There is a U(1) circle isometry but no SU(3) or SU(2) internal Killing algebra.

## 4D Einstein-frame check (no independent scalar imported)

Write b(t)=sqrt(g_yy)=t^-1/2 and the standard 5→4 zero-mode metric decomposition with zero KK vector

\`\`\`text
ds5² = b^-1 dsE4² + b² dy²,
dsE4² = b[-dt²+t(dx₁²+dx₂²+dx₃²)].
\`\`\`

Define **φ=(√3/2)log b=-(√3/4)log t**, merely a reparameterization of the five-dimensional metric component g_yy. The known Einstein-frame action (overall constant omitted) is \`∫√(-gE)[R_E - 2(∂φ)²]\`; no independent matter field was introduced. The reduced field equations are

\`\`\`text
RicE_μν = 2 ∂μφ ∂νφ ; □E φ = 0 .
\`\`\`

The independent checker calculates all 16 entries of RicE and verifies the scalar wave equation exactly, not merely a numerical Friedmann fit.

Einstein cosmic proper time and scale factor are

\`\`\`text
dτ = t^(-1/4)dt ; τ=(4/3)t^(3/4),
aE=t^(1/4) ∝ τ^(1/3),
H_E=1/(3τ), φdot=−1/(√3 τ).
\`\`\`

The Friedmann constraint \`3H_E²=φdot²\` holds exactly. The effective perfect-fluid equation of state from this canonical **metric-derived scalar** is \`w_E=+1\` (stiff), and \`d²a_E/dτ²=−2a_E/(9τ²)<0\`: **deceleration**, not observed late-time acceleration. It is neither a stable-radius vacuum nor an independently postulated scalar model.

**Frame warning:** the naive fixed-y slice has FRW scale factor a_J=t^(1/2) and an Einstein tensor looking like an effective radiation fluid w_J=1/3. That is not the canonical four-dimensional Einstein frame; its Einstein–Hilbert coefficient depends on the shrinking circle b(t). These differing equations of state are frame-dependent geometric interpretations, not two independently generated physical substances. The exact oracle checks the Jordan-slice apparent ratio 1/3 as well.

## Evidence, claims and limitation matrix

- Independent local: \`python -B tools/check_vacuum_kasner5.py\` with SymPy 1.14.0 **PASS**: direct 5D Christoffel→Riemann→Ricci, exact polynomial classification including static edge case, all 25 vacuum components, two independent Kretschmann expressions, 4D metric-derived scalar Einstein equations, proper-time Friedmann/deceleration, and frame comparison. Symbolic arithmetic only; no floating-point approximation or simulated stability.
- Candidate Lean \`lean/Research/VacuumKasner5.lean\`: exactly ten scalar/inequality/branch-classification lemmas. It does **not** kernel-formalize Ricci curvature, Kaluza–Klein reduction, Lorentzian geometry, or a cosmological physical theory. Dedicated pinned \`.github/workflows/vacuum-kasner5.yml\` requests trust-zero, theoremwise axiom allowlist, and independent SymPy with SHA evidence. Exact-head success must be confirmed.
- Mathematical provenance: this is standard Kasner/Kaluza–Klein cosmology, not a novel solution. Overduin & Wesson, *Kaluza–Klein Gravity*, *Physics Reports* **283** (1997), 303–380, https://doi.org/10.1016/S0370-1573(96)00046-4 and https://arxiv.org/abs/gr-qc/9805018 explicitly review such 5D uniform metrics and induced-matter interpretations. For generic KK reduction refer to the *Review of Particle Physics*, extra-dimensions review, https://pdg.lbl.gov/2017/reviews/pdf-files/extradim.pdf . The paper's apparent radiation interpretation does not negate our Einstein-frame scalar w=1.
- Physical obstructions: the solution exhibits classical 4D expansion from **pure higher-dimensional geometry**, but its compactification radius has a runaway, it is curvature-singular, has only Abelian internal U(1), provides no observed accelerating expansion, stable constants, chiral fermions, quantum fields, measured interactions or equivalence-principle tests. Matching one gravitational equation is not reconstruction of existing physics.
- The effective gel branch uses independent memory and field variables and cannot be silently merged into this gravity-only result.

## Decision / next finite research item

**Success (conditional to the ansatz):** time-dependent compact S¹ and external FRW avoid the static Minkowski compactification obstruction while keeping all 5D vacuum field equations and obtaining a finite 4D Einstein-frame gravity kinetic coefficient at each t>0. **Obstruction:** within this three-space-isotropic power-law vacuum ansatz every nonstatic expanding branch forces q=-1/2, Einstein-frame stiff-field deceleration and circle runaway; it is not a stable realistic late-time universe.

**Next smallest test:** permit *non-power-law* homogeneous 5D vacuum functions a(t),b(t) and derive the exact first integral of the full vacuum Friedmann system, classifying whether nontrivial expansion can keep the circle bounded and asymptotically static without matter/flux. First check the differential equations before changing compactification topology, adding a cosmological constant, or introducing new fields. Keep DRAFT; no automatic merge, public release, or new paid service.
