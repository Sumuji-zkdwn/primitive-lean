# One eight-dimensional internal metric: gauge algebra and canonical Spinᶜ index

**Date:** 2026-11-22 (JST). **Status:** explicit mathematical candidate and exact symbolic checks. **Not** a solution of pure twelve-dimensional vacuum gravity or a reconstruction of the Standard Model.

## Basic object and the extra assumptions

Take the compact eight-dimensional manifold

\[
K = \mathbb{CP}^2 \times \mathbb{CP}^1 \times \mathbb{CP}^1,
\]

with a product metric: Fubini–Study on the first factor, a round metric on the second, and a smooth rotationally symmetric *nonround* metric on the third. This selects a particular compactification topology and product metric; that selection has **not** been derived from an action of pure gravity. All factors are compatible with their natural complex structures. K is Kähler and possesses the canonical Spinᶜ structure, though it is not a Spin manifold because CP² is not Spin.

On the last factor use standard polar coordinates away from the poles,

\[
g_\epsilon=d\theta^2 + a(\theta)^2d\varphi^2,
\quad a(\theta)=\sin\theta\,[1+\epsilon\sin^2\theta],
\quad \epsilon=\tfrac1{10}.
\]

The expansion near a pole is \(a(\theta)=\theta+(\epsilon-1/6)\theta^3+O(\theta^5)\), and the other pole behaves analogously, ensuring smoothness on the sphere (no cone singularity). For 0<theta<pi, a>0. Its Gauss curvature is

\[
K_G(\theta)=-a''/a
=\frac{1-6\epsilon+9\epsilon\sin^2\theta}{1+\epsilon\sin^2\theta}.
\]

For epsilon=1/10, K_G(0)=2/5 and K_G(pi/2)=13/11. It varies strictly with u=sin²theta because dK_G/du=2epsilon(4+3epsilon)/(1+epsilon u)^2>0. This nonconstant curvature ensures that a connected isometry preserves the latitudes; the only continuous freedom is azimuthal rotation. Thus the connected isometry group of this factor is SO(2), not SO(3). Exact symbolic checks also give ∫K_G dA=4pi (Gauss–Bonnet) and area=64pi/15.

## Gauge-algebra success (NOT exact global Standard Model gauge group)

The connected isometry Lie algebras of the factors are

- CP², Fubini–Study: \(\mathfrak{pu}(3)\cong\mathfrak{su}(3)\), dimension 8.
- round CP¹: \(\mathfrak{so}(3)\cong\mathfrak{su}(2)\), dimension 3.
- axially deformed CP¹: \(\mathfrak{so}(2)\cong\mathfrak{u}(1)\), dimension 1.

The product has the Lie algebra \(\mathfrak{su}(3)\oplus\mathfrak{su}(2)\oplus\mathfrak{u}(1)\), total dimension 12. In a Kaluza–Klein reduction the Killing symmetries can be interpreted as gauge transformations. However, the actual connected global isometry group is essentially **PSU(3)×SO(3)×U(1)**, not the observed Standard Model gauge group \((SU(3)\times SU(2)\times U(1))/\mathbb Z_6\). In particular fundamental SU(3) triplets and SU(2) doublets do **not** automatically define representations of PSU(3) and SO(3), respectively. A correct lift/central quotient and hypercharge assignments have to be produced, not declared.

For a representation with SU(3) triality \(t\), weak doublet parity \(w\in\{0,1\}\), and integral hypercharge unit \(q_6=6Y\), the standard-model Z6 quotient demands

\[
2t+3w+q_6\equiv0\pmod6.
\]

The exact verifier confirms this for the usual Q_L, u_R, d_R, L_L, e_R, and optional sterile nu_R **when their standard hypercharges are inserted by hand**. This is a consistency test, not a derivation of those charges from a metric.

## Nonzero canonical Spinᶜ Dirac index on the *same* space

Use the standard canonical Kähler Spinᶜ structure, with Spinᶜ Dirac corresponding to \(\bar\partial+\bar\partial^*\). Its index is the holomorphic Euler characteristic. The Hirzebruch–Riemann–Roch theorem gives

\[
\mathrm{ind}\,D^+_{K} = \chi(K,\mathcal O_K)
= \chi(\mathbb{CP}^2,\mathcal O)\chi(\mathbb{CP}^1,\mathcal O)^2
=1.
\]

For the holomorphic line bundle \(\mathcal O(p,q,r)\), the well-known projective-space index formula gives

\[
\mathrm{ind}\,D^+_{\mathcal O(p,q,r)}
=\frac{(p+1)(p+2)}2\,(q+1)(r+1).
\]

For p=q=1,r=0, the index is 6; when p,q,r are nonnegative the holomorphic sections are six-dimensional and under **suitable lifted covering-group actions** transform like a tensor product of SU(3) 3-dimensional and SU(2) 2-dimensional representation spaces (up to dual conventions). But the twisting line bundle \(\mathcal O(1,1,0)\) is a *new discrete choice*, and the necessary equivariant lift/global-group compatibility has not been derived from the metric. The canonical index=1 mode is a singlet, not a physical quark or lepton. **No actual dynamical fermion field or chirality spectrum is inferred from the numerical index alone.**

This is mathematically compatible with the Atiyah–Hirzebruch vanishing theorem: that theorem constrains the **untwisted Spin Dirac index** on suitable circle-symmetric Spin manifolds, while K is non-Spin and the operator is canonical Spinᶜ. Prior literature (e.g. J.A. Bullinaria, Nuclear Physics B 272 (1986) 266) explicitly warns that a nonzero Kähler-related index does not automatically furnish physical spin-1/2 chiral fermions without elementary gauge-field structure.

## A decisive dynamical failure of the naive compactification

The third sphere has **nonconstant curvature**, so it is not an Einstein surface. On a two-dimensional surface \(\mathrm{Ric}=K_G g\); an Einstein metric requires K_G constant. Moreover by Gauss–Bonnet any compact constant-curvature metric on S² has positive curvature and is a round sphere, which restores the SO(3) isometries rather than a single SO(2).

Consequently, the above product K is not an Einstein manifold, and an *unwarped* product of four-dimensional flat Minkowski space with K is **not a solution** of the pure 12-dimensional vacuum Einstein equations. Nor can one fix it by merely adding a single constant cosmological term to the full product Einstein equation, as the internal varying Ricci eigenvalue would not match a constant. This is an exact obstruction to the **specific simple ansatz**, not a no-go theorem for all gravity-only reconstructions. Warps, non-product internal spaces, additional geometric degrees of freedom and/or modified field equations could change the assumptions; each requires fresh proof. Introducing external gauge fluxes as independent matter would abandon the strong gravity-only premise.

## Reproducible boundary

- `tools/check_single_internal_geometry.py`: exact SymPy polar curvature, pole smoothness, Gauss–Bonnet, area, index arithmetic, and six SM Z6 congruences.
- `lean/Research/SingleInternalGeometry.lean`: arithmetic theorems for curvature rational comparisons, index numerator, and group-center congruences. No manifold isometry theorem, Spinᶜ index theorem, or full Einstein PDE has been Lean-formalized here.
- The present result **meets two mathematical criteria simultaneously on one compact manifold** (gauge Lie algebra and nonzero Spinᶜ index) and **fails the unwarped pure-Einstein dynamic criterion**.

## Prior art and sources

- J. Baptista, *Internal symmetries in Kaluza-Klein models* (2024), https://doi.org/10.1007/JHEP05(2024)178, different use of SU(3) as a compactification space.
- J. A. Bullinaria, *Chiral fermions in Kaluza-Klein theory* (1986), https://doi.org/10.1016/0550-3213(86)90002-7.
- Standard Kähler Spinᶜ and Hirzebruch–Riemann–Roch formulae on products of complex projective spaces are external mathematical inputs. They are **not proved** in the accompanying Lean arithmetic module.