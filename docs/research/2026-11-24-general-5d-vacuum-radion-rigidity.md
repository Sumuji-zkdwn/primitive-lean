# 2026-11-24 — Complete homogeneous 5D vacuum circle classification without a power-law ansatz

**Status:** exact analytic classification of every positive C² solution in the stated ansatz; independent local SymPy 1.14.0 test **PASS** for general arbitrary functions, all 25 Einstein vacuum components, first integrals, all solution families, and 4D Einstein-frame equations. This is a special-case rederivation of standard generalized Kasner/Bianchi-I theory, **not original relativity**. The paired Lean module proves **only 11 finite algebraic residual certificates**; its kernel/axiom status must be checked on the dedicated exact-head CI.

## Checkpoint and choice of finite question

The predecessor [draft PR #261](https://github.com/Sumuji-zkdwn/primitive-lean/pull/261) verified the particular 5D Kasner metric with exponent p=1/2 and q=-1/2. The repaired source commit 6ed4b0da1db8a0850b2013441423ccda94c9209e passed dedicated [CI 45286900428](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/45286900428), including 10 Lean theorem/axiom audits and the exact SymPy test. Its all-modules integration run 45286899979 remained in_progress at checkpoint, **not a verified overall PASS**. Its generated-metadata successor e961f804a47eea1828190cbb48a1a3d2d04985fa received action_required, not a failed source test. Earlier pure-vacuum [#260](https://github.com/Sumuji-zkdwn/primitive-lean/pull/260) source f251f656b04f8991c468f6df234c94a0df095f4e had dedicated 45278639134 and integration 45278639027 **SUCCESS**. Historical heads #176–#179 and #183 had action_required source-head checks; no speculative repair of their unexecuted workflows was made.

**The new question**: do any genuinely non-power-law **homogeneous, spatially flat, three-space isotropic** 5D Ricci-flat metrics permit an eternally expanding 3D space and an internal S¹ whose proper radius converges to a finite positive constant, with no added matter or flux?

## Exact ansatz and field equations

On a connected open proper-time interval I with positive smooth (C² is enough) a,b, periodic coordinate χ, spatially Euclidean homogeneous isotropic xᵢ, use only the 5D metric

  ds₅² = -dt² + a(t)² ∑ᵢ₌₁³ (dxᵢ)² + b(t)² dχ².

There is **no assumption** a or b is a power of t, no cosmological constant, extra scalar field, gauge field, fermion, brane, or other non-Einstein source.

Define H=a'/a, F=b'/b and Θ=3H+F. Direct Christoffel/Riemann differentiation gives:

  Ric_tt = -3(H'+H²) - (F'+F²),
  Ric_xixi/a² = H'+HΘ,   i=1,2,3,
  Ric_χχ/b² = F'+FΘ,   all off-diagonal terms vanish.

A direct algebraic combination of these vacuum equations yields the exact constraint

  0 = Ric_tt+3 Ric_xx/a²+Ric_χχ/b² = 6 H(H+F).

The remaining ODEs are

  H'=-HΘ,     F'=-FΘ.

Define the strictly positive spatial four-volume density V=a³ b. Then

  V'/V=Θ,    (VH)'=V(H'+HΘ)=0,
  (VF)'=V(F'+FΘ)=0,   V''=V[Θ'+Θ²]=0.

Thus VH=C_H and VF=C_F are **constant on the connected interval**, and V' = 3C_H+C_F is constant. The Hamiltonian constraint becomes C_H(C_H+C_F)=0 (since V>0). This immediately classifies every positive C² local vacuum solution; there is no missing nonlinear time dependence or switching between the branches.

## Complete solutions within this precise ansatz

1. **Externally static** C_H=0: H=0 identically, so a(t)=A>0. Then b''=0, hence b(t)=ct+d>0 on the selected interval. This includes b constant (entirely static Minkowski₅), and the locally flat Milne-type circle with linear b. For periodic χ, an extension through b=0 generally needs separate global scrutiny; local flatness is not a claim of global completeness.
2. **External evolution** C_H≠0: C_F=-C_H. Thus F=-H at every time, (ab)'=0, and a² b·a=(ab)a²=V is affine. Equivalently (a²)''=0. Therefore for positive normalization constants A,B and constants c≠0,d with ct+d>0 on I,

   a(t)=A sqrt(ct+d),   b(t)=B/sqrt(ct+d).

   This is the **only** externally non-static branch in this class, up to trivial shifts/rescalings. If a'>0 anywhere then c>0 everywhere on the interval, b'<0 everywhere and b(t)→0 as t→∞ on the future-unbounded expanding branch. There can be no moment of stationary circle radius b'=0 while H>0, and no late-time positive radius stabilization. If c<0, the external space contracts on its positive domain; this is the time-reversed counterpart, not expanding.

The result is **stronger than fitting exponents**: it allows arbitrary twice-differentiable time dependence from the outset. It does NOT constrain anisotropic 3D metrics, 3D spatial curvature, off-diagonal metric components, higher-dimensional warped inhomogeneous spaces, or added gravitational cosmological terms.

## Einstein-frame no-acceleration certificate

For the evolving branch, define the standard pure-metric 4D Einstein-frame line element and radion bookkeeping:

  ds₅² = b⁻¹ ds_E4² + b² dχ²,
  ds_E4² = b[-dt²+a² d⃗x²],
  φ=(√3/2)log b.

No primitive scalar is imported: φ is **defined** by g_χχ. Let α=a√b, dτ=√b dt. The proper Einstein-frame expansion is H_E=(H+F/2)/√b. A direct calculation for any positive a,b gives

  (1/α) d²α/dτ² = [H'+F'/2+H(H+F/2)]/b.

In the expanding Ricci-flat branch F=-H, H'=-2H², F'=2H², hence

  (1/α) d²α/dτ² = -H²/(2b) < 0.

Thus the entire *unrestricted-time homogeneous solution class* has no positive 4D Einstein-frame acceleration on the expanding branch. The scalar relation Ric_E,μν=2∂μφ∂νφ, □_Eφ=0 and Friedmann constraint 3H_E²=(dφ/dτ)² are independently checked for the explicit general-constant family. The late-time scale factor still obeys α∝τ^(1/3), equation of state w=1. The variable 4D Einstein coefficient in the raw t-sliced/Jordan frame must not be mistaken for independently postulated matter.

## What is independently machine checked

- Local command: python -B tools/check_general_vacuum_radion5.py (SymPy 1.14.0) — **PASS**, all **25** generic Ricci entries evaluated from independent Christoffel and Riemann computations on a(t), b(t); normalized residual and Hamiltonian factor; V'', (VH)', (VF)' identities; three explicit vacuum branches (25 components each); full 4D Einstein-frame 16 Ricci entries and scalar wave equation, Hubble/Friedmann constraint and strict negative acceleration. All symbolic, no floating point. Script SHA256 f123997c72860d0b7ed03496b5cdf6a352da79d6a90ff1e3fce6bebb4a7b94f5.
- Paper proof (outside Lean): integrating first-order ODEs for V, H, F and observing connected interval + V>0 rules out switching branches. The first-integral classification is an exact mathematical argument, not only checked on samples.
- Lean module Research/General5DVacuumRadion.lean: **11 candidate** polynomial/algebraic implications of Ricci residuals (branch dichotomy, contraction, trace zero, sign of Einstein-frame acceleration). It does NOT kernel-prove Christoffel formulas, continuity/ODE uniqueness, convergence, global geometry, physics or a complete reconstruction. Dedicated CI requests pinned Lean --trust=0, an axiom allowlist and the independent Python oracle. Do not claim CI PASS until the actual run.
- Physical qualification: exactly one Ricci-flat higher-dimensional metric, no extra physical field; pure 4D geometric expansion is obtained, but circle radius runs away, internal isometry is U(1), no acceleration, chiral fermions, measured interactions, quantum states or realistic stabilization. This is an explicit **conditional no-go** only in the stated flat homogeneous isotropic product-circle ansatz.

## Established literature and next task

General vacuum Bianchi I solutions are the classical Kasner family; higher-dimensional KK cosmology is well established, so no priority claim is made. See Overduin & Wesson, *Kaluza–Klein Gravity*, Physics Reports 283 (1997), 303–380, https://arxiv.org/abs/gr-qc/9805018 and DOI https://doi.org/10.1016/S0370-1573(96)00046-4 . A recent accessible derivation of Bianchi-I vacuum volume linearity and Kasner powers appears at https://www.mdpi.com/2073-8994/16/5/564 ; also see https://academic.oup.com/mnras/article/442/3/2331/1047227 for first-order directional Hubble equations.

**Next one finite bounded test:** relax *flat three-space* alone to FRW spatial curvature k∈{-1,0,+1}, preserving 5D Ricci-flat vacuum and homogeneous S¹ with one metric; find any expanding, stable-radius solution and check whether it is just a Milne coordinate description of 4D flat spacetime. Distinguish a geometry-induced effective 4D stress tensor from actual particle content. Keep this independent PR DRAFT; no main merge or release.
