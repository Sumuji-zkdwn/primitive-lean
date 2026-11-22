# 2026-11-23 — Finite SU(2) cube: a localized defect unwinds despite a Skyrme-like quartic

**Status: exact finite counterexample + local SymPy check. Lean kernel compilation and axiom audit are not yet verified on the new PR head.** This is an effective lattice model with an extra quaternion field, not gravity alone. All conclusions below are conditional on the stated discretization; no general no-go for continuum Skyrmions is claimed.

## Previous state and test selection

1. Passive gel draft [#183](https://github.com/Sumuji-zkdwn/primitive-lean/pull/183) is still open, head `8a6ffd4b9d91a5e3f41238da841b2a64b70a846c`. The queried exact-head workflow runs all report `action_required` and no jobs, **not a failed Lean build**. The seven locally declared Lean theorems and Python tests therefore cannot be called CI/kernal verified from those runs.
2. The [#176](https://github.com/Sumuji-zkdwn/primitive-lean/pull/176)–[#179](https://github.com/Sumuji-zkdwn/primitive-lean/pull/179) source heads were checked, respectively `ba1dc78f9be0ca3867fcaeb5b51dde01687c3ff2`, `8a84ab5a623150c1dc2df6f8614e4b5f0df7d485`, `5ce3ddc293417ffea43c79b99b16e36ff1594186`, `cb0549a92dc2d7297093196788d6936f21418098`. Their exact-head dedicated workflows also reported `action_required`, without execution. Do not confuse that with failed proofs.
3. [#193](https://github.com/Sumuji-zkdwn/primitive-lean/pull/193) has already tested the **continuum** Skyrme scale lower bound, which relies on a smooth map from compactified three-space to S³ and a fixed boundary value. [#199](https://github.com/Sumuji-zkdwn/primitive-lean/pull/199) independently checks known exact 5D vacuum Taub–NUT to 4D Einstein–Maxwell–dilaton, with dedicated source-run CI PASS. Neither proves that discretized S³ site values retain a topological sector. The next high-information test is therefore a lattice topological protection challenge.

## Assumptions and criterion

Take an ordinary cube with eight sites V={0,1}³, 12 edges and six elementary square faces. Every site holds q_v∈S³⊂R⁴, a unit quaternion representing SU(2), with **no extra nearest-neighbor admissibility restriction**. For a>0 and b≥0, define the finite lattice energy

E(q) = (a/2) Σ_edges ||q_u−q_v||² + (b/4) Σ_faces (||d_i q||²||d_j q||² − (d_i q·d_j q)²).

The two face differences start at the face's lower-coordinate corner; the quartic is a **Skyrme-like Gram area**, not the full continuum topological Skyrme functional. It is nonnegative by Cauchy–Schwarz. An exact topological sector would require a disconnected admissible component or an infinite barrier. A finite-energy continuous path to vacuum disproves such protection for this model. The test separates static equilibrium, nonradial stability and dynamics.

## Explicit exact counterexample

Set all q_v=(1,0,0,0) except the origin, initially q_0=(-1,0,0,0). For 0≤s≤1 let

D(s)=s²+(1−s)²=2(s−1/2)²+1/2 > 0,

q_0(s) = ((2s−1)/D(s), 2s(1−s)/D(s), 0, 0).

The polynomial identity (2s−1)²+[2s(1−s)]²=D² ensures every q_0(s) is a unit quaternion. For each of the six faces, its two edge-difference vectors are equal or zero all along this path. Their Gram determinant therefore vanishes **identically**. Only three quadratic edges contribute, so

E(s) = 3a[1−(2s−1)/D(s)],

E(0)=6a, E(1/2)=3a, E(1)=0,

E′(s) = −12a s(1−s)/D(s)² < 0 for 0<s<1.

This is a strictly energy-descending path from the local antipode to vacuum, independent of how large the positive quartic coefficient b is.

The initial configuration is a constrained stationary point: at q_v=±1 each quadratic edge gradient is parallel to its S³ site normal; the zero Gram quartic also has zero first derivative. But it is **unstable to an admissible single-site perturbation**, not restricted to a radial continuum hedgehog ansatz. Rotate the origin alone through q_0(θ)=(cosθ,sinθ,0,0), leave the other seven sites fixed. All quartic faces remain zero. Along this allowed direction, E(θ)=3a(1−cosθ), E′(π)=0 and E″(π)=−3a<0. The constrained Hessian thus has a negative direction. With positive kinetic mass, the linearized conservative dynamics has an unstable exponential mode; a gradient relaxation has a growing mode. This does not simulate the independent delayed-memory system of #183.

## General finite-graph obstruction

For any finite N, the unconstrained site configuration space (S³)^N is path-connected. To connect any q=cosθ·1+sinθ·u to the identity, with unit imaginary u and θ∈[0,π], use q(t)=cos((1−t)θ)·1+sin((1−t)θ)·u (choose any u for the antipode). Repeat at each site. A continuous integer-valued charge on this connected space is constant, so an exact nontrivial integer winding sector cannot be defined from unconstrained site quaternions alone.

Moreover, for any unit quaternions, ||q_u−q_v||²≤4, and each face Gram determinant is between 0 and 16. Thus on this cube 0≤E(q)≤24a+24b for all configurations, a finite barrier bound. **This does not rule out metastable lattice minima**. One may restore genuinely distinct sectors by adding a valid interpolation/hard-admissibility rule or singular boundary, but that new condition is a substantive, separately audited assumption.

There is no contradiction with continuum degree theory, where q:R³∪{∞}≈S³→S³ is a continuous field with fixed value at infinity. The unqualified lattice sample has discarded essential topology.

## Evidence and strict limits

- The independent offline run of `python -B tools/check_finite_skyrme_unwinding.py` with SymPy 1.14.0 succeeded 2026-11-23 JST. It enumerates **all 8 sites, 12 edges and 6 faces**; symbolically checks the unit path, exact edge energy, zero face energy for all s, three endpoint energies, derivative sign formula, tangent stationary point and E″(π)=−3a. The topology generalization is a mathematical argument, not numerically proved by a loop.
- `lean/Research/FiniteSkyrmeUnwinding.lean` contains **eight candidate elementary Lean theorems**: rational numerator identity, denominator positivity, rank-one Gram algebra, three endpoint energies, strict energy drop and unit-edge norm bound. It does **not** kernel-formalize the whole cube, topology, or a full Skyrme field theory. No local Lean executable was available. Dedicated `.github/workflows/finite-skyrme-unwinding.yml` requests pinned `--trust=0`, theoremwise `#print axioms`, explicit allowlist and independent SymPy; success needs confirmation on exact head.
- **Physics review:** independent SU(2)-valued site variables are *not derived from a metric*. The cube selects a preferred frame, no exact Lorentz invariance/general covariance is shown, and neither conserved relativistic stress energy, the equivalence principle, the physical spinor spectrum nor a quantum theory follows. A local instability is not an observed particle.

**Next one finite test:** choose an explicit geometric interpolation or hard admissibility rule on a single lattice cell; verify whether it prevents this exact unwinding path and whether any resulting energy barrier is finite, parameter dependent, or imposed by hand. Keep this branch draft and do not merge main automatically.

## Established literature, not original claims

- C. Adam and A. Wereszczynski (2014), *Topological energy bounds in generalized Skyrme models*, https://doi.org/10.1103/PhysRevD.89.065010
- Y. Yang (2023), *Skyrme model and related topics*, https://doi.org/10.1093/oso/9780192872616.003.0012
- T. Waindzoch and J. Wambach (1995), *Stability of the B=2 hedgehog in the Skyrme model*, https://arxiv.org/abs/hep-ph/9509421 — a precedent that radial tests do not exhaust shape instabilities.
