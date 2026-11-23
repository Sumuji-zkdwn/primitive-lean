# Tangent-probability observability: regular locus and a finite-word obstruction

Date: 2026-11-23. Follow-up to draft PR #232. The differential and stability results below are **paper proofs**, not automatically Lean-certified. A separate module `Research.SiphonTangentObservation` attempts a kernel-checked proof of the prior five-read injectivity; verify its exact-head CI before claiming success.

## Maps and five probability reads

Use the existing polynomial maps:

\[
r=I(u,v)=v+u^3,\qquad
E(u,v)=(u+r^2,\ r-(u+r^2)^3),\qquad
L(u,v)=(v,v-u).
\]

The transformation from \((u,v)\) to \((u,r)\) is a polynomial coordinate change with determinant one. Each level set \(r=\mathrm{const}\) has tangent \((1,-3u^2)\), giving the squared normalized first-coordinate weight

\[
h(u)=\frac{1}{1+9u^4}.
\]

The observation map used in PR #232 is

\[
\Phi(z)=\left(h(z_1),h((Ez)_1),h((E^2z)_1),h((Lz)_1),h((E(Lz))_1)\right).
\]

PR #232 contains the original real-algebraic injectivity argument.

## Theorem 1: differential rank exactly two off the origin

**Statement:** \(\operatorname{rank}D\Phi(z)=2\) for every \(z\ne(0,0)\), while \(D\Phi(0,0)=0\).

**Proof:** Work in \((u,r)\) coordinates and write \(a=r^2\). The first three observations are \(h(u+na)\), \(n=0,1,2\). Their gradients are

\[
\nabla h(u+nr^2)=h'(u+nr^2)(1,2nr),\qquad
h'(x)=\frac{-36x^3}{(1+9x^4)^2}.
\]

For \(n<m\), the corresponding \(2\times2\) minor equals

\[
2r(m-n)h'(u+nr^2)h'(u+mr^2).
\]

For \(r\ne0\), the three numbers \(u,u+r^2,u+2r^2\) are distinct, so at least two are nonzero. Choose those indices; the minor is nonzero. For \(r=0,u\ne0\), use the first and fourth observations, \(h(u)\) and \(h(v)=h(r-u^3)\). Their minor in \((u,r)\) coordinates is \(h'(u)h'(-u^3)\ne0\). At the origin all observed first coordinates are zero and \(h'(0)=0\); every row vanishes. This covers all cases.

**Consequence:** With five-read injectivity from PR #232, \(\Phi\) is a smooth embedding of the punctured plane into \(\mathbb R^5\). Every compact \(K\subset\mathbb R^2\setminus\{0\}\) has constants \(0<c_K\le C_K\) such that

\[
c_K\|z-w\|\le\|\Phi(z)-\Phi(w)\|\le C_K\|z-w\|\quad(z,w\in K).
\]

To prove the lower bound, use the inverse-function theorem on a nonzero two-output minor for near-diagonal pairs; away from the diagonal, the continuous quotient of distances has a positive minimum by injectivity and compactness. The upper bound follows from smoothness on a compact neighborhood. The full map is a **topological** embedding too: the first and fourth outputs \(h(u),h(v)\) being positive and convergent to their values at a fixed point force inputs to remain bounded, and injectivity determines all cluster points. Nevertheless it is not an immersion at the origin.

## Theorem 2: no finite E/L observation schedule repairs the origin

Let \(W\) be any **finite** set of operation words built only from \(E\) and \(L\). Both maps fix the origin; hence each composite \(w\in W\) is a polynomial fixing the origin. Put \(q_w(z)=(w(z))_1\), so \(q_w(z)=O(\|z\|)\) near zero. The exact identity

\[
1-h(q)=\frac{9q^4}{1+9q^4}
\]

implies for the vector of readings \(\Phi_W(z)=(h(q_w(z)))_{w\in W}\)

\[
\|\Phi_W(z)-\Phi_W(0)\|=O(\|z\|^4).
\]

Thus \(D\Phi_W(0)=0\) for **every finite W**. If an inverse exists on the image, it cannot be locally Lipschitz at the origin: otherwise \(\|z\|\le C\|\Phi_W(z)-\Phi_W(0)\|\le C'\|z\|^4\), impossible as \(z\to0\) through nonzero points. An inverse Hölder estimate of exponent \(\alpha>1/4\) is impossible for the same reason.

For the *particular* five-word signature, the pair \(z_t=(t,-t^3)\), \(w_t=(-t,t^3)\) from PR #232 has equal first four observations and fifth gap asymptotic to \(72t^9\) at \(t\to0^+\), although their state separation is asymptotic to \(2t\). Hence no local inverse Hölder estimate with exponent \(\alpha>1/9\) holds for this five-word signature.

These are obstructions for **this sensor and words in these two fixed-point maps**, not impossibility results for an arbitrary probabilistic sensor, an affine offset, or an infinite adaptive observation scheme.


## Theorem 3: at least three scalar tangent-probability reads are needed globally

For any choice of **two** operation words, the corresponding map to \(\mathbb R^2\) is continuous and sends the origin to \((1,1)\). Both components of every observation satisfy \(h(q)\le1\), so the whole image lies in \((0,1]^2\). If this map were injective on \(\mathbb R^2\), invariance of domain would imply that its image is open in \(\mathbb R^2\); this contradicts the presence of its point \((1,1)\), which cannot have a neighborhood contained in \((0,1]^2\). Thus **two scalar reads can never be globally injective** with this sensor and common fixed point; one read also cannot be globally injective. Together with five-read sufficiency, this gives the rigorous bound \(3\le N_{\min}\le5\) for the minimal number of fixed-word readings (whether three or four suffice remains open).

A cautionary finite-grid check: the **single** word \(E\,L\,E\), applied left to right, gives distinct squared first-coordinate readings at all 49 integer-grid states and all 169 half-integer-grid states in the accompanying regression. This does **not** contradict the theorem: separation on a finite grid is not global injectivity on the continuum.

## Frame dependence and limitations

The normalized squared minors depend on the chosen coordinate frame. Without extra structure, the group \(\mathrm{GL}_D(\mathbb R)\) acts transitively on \(d\)-planes in \(\mathbb R^D\), so there is no nonconstant **scalar** invariant of a bare \(d\)-plane under every change of basis. Any useful distribution needs a specified sensor/frame/metric or a covariant transformation rule. The present construction does not prove the manifold hypothesis or recover an unknown manifold without extra assumptions.

## Reproducible checks

Run:

```sh
python3 -B -m unittest discover -s tests -p 'test_siphon_distribution_regularity.py' -v
python3 -B tools/verify_toolchain_modules.py --module Research.SiphonTangentObservation
```

The Python checker tests rational exact minors at 169 \((u,r)\) pairs, the quartic identity, 63 finite words fixing the origin, and the hard-to-distinguish state family. It does not substitute for the real proof.

The Lean module `SiphonTangentObservation` has proof declarations `five_square_reads_injective` and `five_probability_reads_injective`; their certification depends on a successful pinned-Lean exact-head source/axiom audit. The rank classification, finite-word no-go, and compact stability remain paper proofs unless separately formalized.

**Next task:** compare an alternate sensor with a nonvanishing first derivative at the origin or add a non-fixed-point operation, keeping the distinction between coordinate-dependent measurements and coordinate-free geometric invariants.
