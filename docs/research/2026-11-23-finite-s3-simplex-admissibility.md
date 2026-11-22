# 2026-11-23 — Finite S³ simplex: an exact geometric admissibility wall

**Scope:** One bounded follow-up to [draft #203](https://github.com/Sumuji-zkdwn/primitive-lean/pull/203). Local SymPy 1.14.0 rational/linear-algebra oracle **PASS**; 12 *candidate* Lean algebraic lemmas added. Dedicated exact-head CI and axiom audit **not yet verified**. The topological degree argument invokes standard external topology, not a Lean-kernel proof.

## 1. Question and previous checkpoint

[#203](https://github.com/Sumuji-zkdwn/primitive-lean/pull/203) exhibits a one-site SU(2)=S³ deformation on an eight-vertex cube that reaches vacuum with strictly decreasing quadratic energy and identically vanishing Skyrme-like quartic. On the unconstrained finite product (S³)^N there are no nonconstant continuous integer charges. **Finite question:** Does an *explicit* simplex-wise interpolation/admissibility rule restore honest discrete winding sectors? If so, does that follow from a finite smooth energy or from an imposed hard exclusion?

Queried source head of #203: `cc6a1c7cc942b4057a05f5381b7c47077abe0b07`; dedicated run 45079346300 is `action_required` (no executed kernel job). Queried heads of #183, #176, #177, #178, #179 respectively: `8a6ffd4b9d91a5e3f41238da841b2a64b70a846c`, `ba1dc78f9be0ca3867fcaeb5b51dde01687c3ff2`, `8a84ab5a623150c1dc2df6f8614e4b5f0df7d485`, `5ce3ddc293417ffea43c79b99b16e36ff1594186`, `cb0549a92dc2d7297093196788d6936f21418098`. Their queried dedicated source runs remain `action_required`, **not compiler failures**. Do not misreport them as PASS.

## 2. Exact finite construction

The **domain** is the boundary of the four-simplex Δ⁴, the five-tetrahedron minimal triangulation of S³; it has five vertices and ten edges. The **target** is S³⊂R⁴ of unit quaternions, SU(2) as a manifold. Choose five rational unit target vectors

```text
v0=(1,0,0,0), v1=(0,1,0,0), v2=(0,0,1,0),
v3=(0,0,0,1), v4=(-1/2,-1/2,-1/2,-1/2).
```

At each vertex the unit-quaternion field is `q_i(t)=w_i(t)/||w_i(t)||`, with `w0=v0` and `wi(t)=(1-t)vi+t v0` for i=1,…,4, t∈[0,1]. The squared norms are 1, `2t²−2t+1` (i=1,2,3) and `3t²−3t+1` (i=4), all strictly positive. Thus the **five site values move continuously** from a nontrivial configuration to the all-v0 vacuum.

**Hard geometric admissibility:** for each tetrahedral face F with four site values, require `0 ∉ conv{q_i : i∈F}`. Under this *extra* condition, the piecewise **normalized affine** interpolation `f(x)=(Σ_{i∈F} λ_i q_i)/||Σ λ_i q_i||` exists everywhere, agrees on common faces and defines `f:∂Δ⁴→S³`. It can carry an integer Brouwer degree. Positive rescaling of each vertex (`wi→qi`) preserves whether its facet's positive cone contains zero, and the two radial interpolations are homotopic when admissible.

The five unnormalized facet determinants, indexed by the **omitted vertex**, are exactly

```text
D0=(t−1)^3(6t−1)/2
D1=(t−1)^3/2
D2=−(t−1)^3/2
D3=(t−1)^3/2
D4=−(t−1)^3.
```

Thus all facets are admissible when `0≤t<1` and `t≠1/6` (invertibility is a sufficient condition here). At `t=1` all vertex values are v0, so the facets again satisfy admissibility even though determinants vanish.

## 3. Wall crossing and degree, with exact witnesses

The full affine simplex `P_t=conv(w0,…,w4)` has affine determinant `3(t−1)^4`, nonzero for `t<1`. The unique barycentric preimage of the origin is

```text
lambda0=(1−6t)/(6(1−t))
lambda1=lambda2=lambda3=1/(6(1−t))
lambda4=1/(3(1−t)).
```

For `0≤t<1/6` all five coefficients are positive and sum to one. Thus 0 lies in the **interior** of P_t and the radial projection of its boundary has degree +1 or −1 (depending on domain orientation). The same is true for the normalized-vertex interpolation.

Exactly at `t=1/6` the zero hits the face opposite vertex 0. Explicitly,

```text
(w1 + w2 + w3 + 2 w4)/5 = 0.
```

All four weights are strictly positive. Positive rescaling supplies an equivalent convex-zero witness for the unit q_i. The normalized affine map is **undefined at an interior point of this tetrahedron**. This is the unique forbidden t along the explicit site path.

For `1/6<t≤1`, let `L=(5,−1,−1,−1)`. Then `L(w0)=5` and `L(wi)=6t−1>0` for all moving vertices; the entire interpolated image lies in one open hemisphere. Hence the map has degree 0; at t=1 it is constant. **An admissible homotopy cannot connect the two degrees**, by the standard homotopy invariance of degree. This is a real, but *assumption-dependent*, finite topological obstruction.

The finite quadratic edge energy `E₂=(a/2) Σ_{i<j} ||qi−qj||²` is globally bounded `0≤E₂≤20a` for a≥0, including at the forbidden wall. At t=0 it equals `12a`. The forbidden crossing is therefore **not** an infinite barrier created by this smooth energy: it exists only because a geometric singular configuration was expressly removed. Continuous finite polynomial Skyrme-like site/face energies are likewise bounded on the compact finite configuration space; they do not independently impose this hard exclusion.

## 4. Independently executable checks and limits

- `python -B tools/check_finite_s3_admissibility.py` with SymPy 1.14.0 locally **PASS**: all 5 unit vectors, 5 facet determinants, normalization positivity, strictly interior barycentric values, exact zero at t=1/6, separating hyperplane after t=1/6, K5 energy bound. All exact rational/polynomial operations; no tolerance/floating-point threshold.
- `lean/Research/FiniteS3SimplexAdmissibility.lean`: 12 candidate polynomial/inequality identities for barycentric certificates, wall t=1/6, separating form and norms. It does **not** construct a simplicial 3-sphere or prove topological degree, nor check a full physical continuum field. Pinned `--trust=0`, theorem-by-theorem axiom audit and exact SymPy steps are requested by `.github/workflows/finite-s3-admissibility.yml`; **kernel CI status must be checked on the new head before claiming success**.
- Mathematics: Brouwer degree, radial projection of the boundary of a convex polytope containing 0, and degree invariance are established external theorems. This is a concrete finite witness and counterexample to the assertion that arbitrary site data alone carry protected integer sectors, **not a new general topological theorem**.
- Physics: the site quaternions are an independent SU(2)-valued field **not derived from a higher-dimensional gravitational metric**. The hard interpolation constraint is an additional assumption. There is no Lorentz-invariant dynamical vacuum, Einstein derivation, equivalent stress energy, spectrum of fermions, quantization, or realistic particle stability here. It does not rescue the original gravity-only hypothesis.

## 5. Related literature and next finite task

B. Berg and M. Lüscher, *Definition and statistical distributions of a topological number in the lattice O(3) σ-model*, Nucl. Phys. B 190 (1981) 412–424, https://doi.org/10.1016/0550-3213(81)90568-X — precedent for **geometric lattice topological charge** (for two-dimensional O(3), not this four-simplex/S³ instance). General radial-projection/degree constructions predate this calculation; e.g. the standard convex-polytope radial homeomorphism appears in topology lecture notes, https://viktorajstein.github.io/files/Topo_Skript_WiSe2122.pdf, Example 1.2.4. No priority or novel physical discovery claimed.

**Next one bounded test:** replace the hard forbidden wall with a specified *smooth* extra energy term on the same five-vertex model, and check whether its barrier diverges or remains finite near t=1/6. Distinguish an artificially singular penalty from a term derivable from a higher-dimensional Ricci-flat metric. In parallel keep the truly metric-only branch separate. DRAFT PR only; no auto-merge or release.
