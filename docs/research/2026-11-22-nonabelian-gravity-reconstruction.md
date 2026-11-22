# Gravity-only reconstruction: non-Abelian structures and the next real obstruction

Date: 2026-11-22 (JST). Research-stage report, with independent exact finite and symbolic tests.

## Scope

Goal: start with geometry (a metric and its compatible operations), not separately stipulated matter / electromagnetic / nuclear forces; determine rigorously what existing interactions can be reconstructed. This report records two independently verified mathematical witnesses. They **do not** constitute an experimentally complete theory or recovery of the Standard Model. The constructions are standard in parts; the value is a checkable synthesis tied to observer equivalence, intrinsic/extrinsic distance, and holonomy.

## A. Gauge-equivalent 18-point geometries and non-Abelian holonomy

Take the base triangle V={0,1,2} and fibre G=S3 (six permutations of three labels), creating 18 points V×G. Attach to each oriented base edge i→j a transport U_ij∈G, with U_ji=U_ij⁻¹. Horizontal lifted edges connect (i,g) to (j,U_ij g). Vertical edges connect (i,g) to (i,gs) and (i,gt) for fixed transpositions s=(01), t=(12). Because these generators are involutive and reverse base transport is the inverse, the graph is undirected; its shortest-path metric is an actual finite metric.

Relabel each fibre by a local choice h_i∈G: (i,g)↦(i,h_i g). Under this change the link becomes U'_ij=h_j U_ij h_i⁻¹. It is an exact graph isomorphism: horizontal and vertical adjacency, all lifted distances, and all ordinary toppling rules that depend only on adjacency are preserved. The triangle holonomy H=U_20 U_12 U_01 is conjugated: H'=h_0 H h_0⁻¹. In particular, the order of H is invariant.

- Flat assignment U=(e,e,e): order(H)=1.
- Twisted assignment U=(s,t,e): H=ts is a 3-cycle, order(H)=3.
- In the two cases, histograms of ordered-pair distances in 18-point lift are respectively `{0:18,1:72,2:108,3:90,4:36}` and `{0:18,1:72,2:144,3:90}`. Thus they cannot be related by graph isometry, despite having the same 3-point visible base.
- Full exact check: all 216 choices of link triples and all 216 independent local fibre gauge choices (46,656 cases) preserve the loop conjugacy and graph adjacency, for all 18 points.

This provides a finite analogue of a non-Abelian connection reconstructed from **geometry of a lifted fibre**; it is not yet continuous Yang-Mills dynamics. It also yields a direct testable claim for sandpile observers: gauge-equivalent lifts have corresponding chip patterns under graph relabeling; distinct holonomy sectors may differ in dynamics.

## B. Continuous non-Abelian connection and metric covariance

Let T1,T2,T3 be the standard 3×3 skew matrices for so(3), with [T1,T2]=T3 (Lie algebra locally isomorphic to su(2)). Put A_x=a T1 and A_y=b T2. The potentials are coordinate-constant, yet the curvature is nonzero:

    F_xy = ∂x A_y - ∂y A_x + [A_x,A_y] = ab T3.

This is intrinsically non-Abelian: a constant Abelian potential has zero curvature. With a smooth gauge transformation h(x), the transformed connection `A' = h A h⁻¹ - dh h⁻¹` satisfies `F' = h F h⁻¹`. Using the rational rotation `cos θ=(1-x²)/(1+x²), sin θ=2x/(1+x²)`, SymPy verified the exact 3×3 matrix identity and gauge-invariant `tr(F²)=-2a²b²`.

The geometry behind the continuous construction is a Kaluza–Klein bundle metric

    g_hat = g_base + ell² <ω + A, ω + A>,

where `ω` is the fibre Maurer–Cartan form and `<>` an Ad-invariant inner product. Under local changes of fibre coordinates, `ω+A` changes by conjugation, preserving `g_hat`. This metric relation is algebraically checked in the matrix model; **it is not shown to solve higher-dimensional vacuum Einstein equations for arbitrary A**. Indeed, constant noncommuting A_x,A_y generically do **not** satisfy the vacuum Yang–Mills equations.

## C. Source-free SU(2) Yang–Mills solution from four-dimensional spin geometry

Use the round S4 metric on a stereographic R4 patch, conformal to the Euclidean metric:

    g_μν = Ω² δ_μν,  Ω(x)=2/(1+|x|²).

The torsion-free spin connection in orthonormal frame `e^a=Ω dx^a` is

    ω_μ^{ab}=δ^a_μ ∂_b log Ω - δ^b_μ ∂_a log Ω.

Project the spin connection using self-dual 't Hooft symbols η^i_ab and a suitable orientation convention. The resulting SU(2) gauge potential is the BPST instanton

    A_μ^i = 2 η^i_{μν} x_ν/(1+|x|²),

with curvature

    F_μν^i = -4 η^i_{μν}/(1+|x|²)².

The curvature is nonzero, self-dual under Hodge star on 2-forms, and obeys the **source-free Yang–Mills equation** `D^μ F_μν=0`. The projection sign depends on the Lie algebra generator convention: in the explicit frame above, `A = -(1/2)η·ω` for the adopted ε structure constants. The smooth data here are fixed entirely by a metric and its torsion-free connection; this is a standard geometric relation, not a new solution.

Exact independent SymPy computation verified:
- the spin-connection projection in all 12 `A_μ^i` components;
- 18 `F_μν^i` components for μ<ν;
- all 18 self-duality identities;
- all 12 Yang–Mills component equations;
- nonzero curvature and squared norm `Σ_{iμν}(F_μν^i)²=192/(1+|x|²)^4`.

**Boundary:** This is **Euclidean** S4, not Lorentzian physical spacetime. Producing an SU(2) YM solution is not reconstructing QCD or electroweak theory, does not give their representations/couplings or chiral quantum matter, and does not prove Einstein–Yang–Mills dynamically equivalent for arbitrary solutions.

## D. A concrete topology trap: a seven-dimensional internal space

A seemingly compact 11-dimensional starting point is spacetime M4 times K7=CP²×S²×S¹. The three internal factors have isometry **Lie algebras** su(3), su(2), and u(1), respectively; this makes the gauge algebra dimension 8+3+1=12. However, their global groups are generally quotients (`PSU(3)` and `SO(3)` instead of simply connected `SU(3)` and `SU(2)`). Whether matter in fundamental doublet/triplet representations descends is a separate global question.

More decisively, CP² has nonzero second Stiefel–Whitney class. Its tangent first Chern class is `c1(TCP²)=3H`, so `w2=H mod 2 ≠0`; hence **CP² is not spin**. Therefore the product K7 is not spin and an ordinary global spinor bundle does not simply exist over the naive product background. A spin^c twist can address this but requires additional bundle data, which must be derived or admitted explicitly. The parity arithmetic is not itself a formal proof of CP² topology; it is a standard topological theorem used as a precise veto on this simple ansatz.

This is an actual obstruction to the economical reconstruction from a metric and standard spinors, not a proof that *all* gravity-first constructions fail. There are other internal geometries and constructions, including non-Killing symmetries and Spin^c structures, but they must be analyzed with the same discipline.

## E. The user's sandpile-pattern test detects hidden holonomy

Treat the entire 18-point lifted finite geometry as a dissipative Abelian sandpile graph. Each vertex has four internal neighbours (two horizontal, two vertical) plus one sink edge, so the toppling threshold is 5. An observer reads only the three base-site aggregate chip counts, discarding all six fibre labels within each base site.

For the controlled input adding n chips at lifted point (0, identity), the flat vs twisted holonomy sectors yield identical base aggregates for every n=0,...,40. The first difference in this specified protocol is n=41:

| Input | Stable visible 3-site pattern | Total sink loss |
|---|---|---|
| Trivial holonomy, 41 grains | (12,7,7) | 15 |
| Order-3 holonomy, 41 grains | (10,9,9) | 13 |

This is a deterministic exact integer-arithmetic counterexample to any claim that observing only base-site coordinates makes hidden internal holonomy forever unobservable. The base sums are unaffected by any fibre relabelling. The independent Python checker verifies all 216 local gauge changes for both connections, with exact covariance of their full stable patterns and sink counts. It also verifies equality of two legal toppling priorities for the tested input range 0..64.

The threshold 41 is not universal: it is minimal for the one specified initial state and observation protocol. The results are bounded finite checks, not newly Lean-proved theorems about Abelian sandpiles or black holes.

Program: tools/check_holonomy_sandpile.py, using tools/check_nonabelian_geometry.py. This bridges dual-metric/observer/sandpile questions to an explicit non-Abelian holonomy experiment.
## Proof/evidence mapping

- `lean/Research/NonAbelianMetricHolonomy.lean`: arbitrary-group link gauge covariance, holonomy conjugacy, lifted-graph covariance and inverse fibre relabeling; explicit noncommuting S3 witness.
- `lean/Research/SpinYangMillsWitness.lean`: exact finite 't Hooft symbol antisymmetry and self-dual algebra.
- `tools/check_nonabelian_geometry.py`: exact exhaustive 46,656-case discrete gauge test + matrix so(3) gauge covariance and curvature.
- `tools/check_holonomy_sandpile.py`: exact first-distinguishing load 41; full local frame checks and priority variations.
- `tools/check_spin_instanton.py`: exact 12+18+18+12 component SymPy check on a stereographic S4 patch.
- Pinned CI workflow compiles Lean with `--trust=0`, audits axioms, and executes both independent Python oracles. No full infinite-dimensional Lean proof of S4 curvature/PDE or Einstein field equations is claimed.

## Next hard milestone

The new problem is no longer merely “can curvature behave like a gauge field?”—yes, rigorously. It is: Can one specified gravitational action, topology, and quantum rule yield **the experimentally correct chiral SU(3)×SU(2)×U(1) matter spectrum and masses** without importing independent gauge/matter primitives? A concrete next bounded test is to compute the index of the relevant internal Dirac operator on a **spin** candidate manifold, and check anomaly cancellation under the induced global gauge group, before attempting any claimed Standard Model reconstruction.

## Sources

- J. Baptista (2024), Internal symmetries in Kaluza–Klein models, JHEP 2024(5)178, https://doi.org/10.1007/JHEP05(2024)178 .
- J. Baptista (2026), Chiral interactions of fermions and massive gauge fields in Kaluza–Klein models, JHEP 2026(5)008, https://doi.org/10.1007/JHEP05(2026)008 .
- E. Witten (1981), Search for a realistic Kaluza–Klein theory, Nucl. Phys. B 186:412–428, https://doi.org/10.1016/0550-3213(81)90021-3 .
- Gauge theory reference for BPST, R. Grady, Gauge Theory Notes (2025), https://math.montana.edu/rgrady/documents/Gauge_Notes_Dec25.pdf .
- Spin structure and characteristic classes: Milnor & Stasheff, *Characteristic Classes*, Princeton (1974), and https://qft.org/mathematical-methods/spin-topology/ .