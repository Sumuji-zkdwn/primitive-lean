# General Gibbons–Hawking jets, unrestricted classical KK/EMD reduction, and Taub–NUT centre

Date: 2026-11-23 JST. Follow-on to [draft PR #215](https://github.com/Sumuji-zkdwn/primitive-lean/pull/215) and [draft PR #199](https://github.com/Sumuji-zkdwn/primitive-lean/pull/199).

**This is a staged verification package, not a claim that three manifold-level theorems are fully kernel-formalized.** The independent SymPy calculations are exact identities in arbitrary local jets; the Lean modules formalize the specific algebraic sublemmas described below. Existing classical results are not new physics.

## 1. General local Gibbons–Hawking theorem — universal 2-jet oracle

Let \(U\subset\mathbb R^3\) be open, \(H:U\to\mathbb R_{>0}\) smooth and \(A\) a local one-form satisfying

\[dA=*_{\mathbb R^3}dH \quad\text{equivalently}\quad \nabla\times A=\nabla H.\]

The metric on a local circle-fibration coordinate patch is

\[G_5=-dt^2+H\delta_{ij}dx^i dx^j+H^{-1}(d\psi+A_i dx^i)^2.\]

Since \(d^2A=0\), the monopole equation forces \(\Delta H=0\). The independent checker `tools/check_kk_gh_universal_2jet.py` represents **every trace-free symmetric second jet** of \(H\) at a point by

\[H(x)=h+p\cdot x+\tfrac12 x^TQx,\quad h>0,\ Q=Q^T,\ \mathrm{tr}(Q)=0.\]

It uses the *canonical homotopy gauge*

\[A(x)=-\tfrac12 x\times p-\tfrac13 x\times(Qx).\]

This satisfies \(\nabla\times A=\nabla H\) as a polynomial identity. The code builds the value, all first and all second derivatives of the **original** 5×5 metric at the centre of the coordinate chart, constructs the derivative of the inverse, the Levi-Civita connection and its first derivatives and **all 25 Ricci components**. All 25 vanish identically as rational functions of **nine independently symbolic parameters** \(h,p_1,p_2,p_3,Q_{11},Q_{12},Q_{13},Q_{22},Q_{23}\). No grid sampling is used.

To turn this jet certificate into a proof for *all smooth* \(H,A\), one still has to justify (in Lean) the local Poincaré lemma/gauge normal form and naturality of the second-jet Ricci construction, as well as prove the algebraic 25-component cancellation in Lean. Those steps are currently external geometric mathematics; this oracle does **not** imply an arbitrary-H Lean theorem.

Lean module `KKGeneralGHBoundary.lean` kernel-checks the universal `div(curl)=0` mixed-partial cancellation, conditional harmonicity and the canonical first curl coefficients.

## 2. General 5D vacuum ⇔ 4D EMD reduction — off-shell universal jets

Assume a circle-invariant, nonsingular 5D spacelike fibre (all fields independent of \(\psi\)) and a 4D Lorentzian metric \(g\), potential \(A\), scalar \(\phi\). Write \(q=e^{\phi/\sqrt3}>0\) and

\[G_5=qg_{\mu\nu}dx^\mu dx^\nu+q^{-2}(d\psi+A)^2.\]

The 4D action, after circle integration **and discarding a total divergence**, is

\[S_4\propto\int\sqrt{-g}\,[R_4-\tfrac12(\partial\phi)^2-\tfrac14q^{-3}F^2]d^4x,\quad F=dA.\]

Define the **off-shell** residuals, not assuming any 4D equations:

\[
\begin{aligned}
E_{\mu\nu}&=R_{\mu\nu}(g)-\tfrac32\partial_\mu\log q\,\partial_\nu\log q
  -\tfrac12q^{-3}(F_{\mu\rho}F_\nu{}^\rho-\tfrac14g_{\mu\nu}F^2),\\
M^\nu&=\nabla_\mu(q^{-3}F^{\mu\nu}),\\
S_0&=\Box_g\log q+\tfrac14q^{-3}F^2.
\end{aligned}
\]

At any point choose 4D Lorentzian **normal coordinates** and the local circle gauge \(A(p)=0\). In that gauge, the exact **componentwise** relation is

\[
R^{(5)}_{\mu\nu}=E_{\mu\nu}-\tfrac12g_{\mu\nu}S_0,\qquad
R^{(5)}_{\mu5}=-\tfrac12g_{\mu\nu}M^\nu,\qquad
R^{(5)}_{55}=q^{-3}S_0.
\]

The independent checker `tools/check_kk_emd_universal_jets.py` verifies **all 25 entries** from the metric, for **independent** values, first and second jets of \(q\), \(A\) and the 4D metric, with no EMD equation imposed. It also contracts the complete 5D scalar and obtains

\[\sqrt{-G_5}R_5=\sqrt{-g}\left(R_4-\tfrac32(\nabla\log q)^2-\tfrac14q^{-3}F^2-\Box_g\log q\right).\]

In particular \(R^{(5)}_{AB}=0\iff E_{\mu\nu}=M^\nu=S_0=0\) under the stated nondegeneracy hypotheses, as a **general classical local statement**. The scalar EMD residual in PR #199 notation is \(\sqrt3 S_0\). The calculation is exact and *off shell*; it is not a re-check of a single EMD solution.

The Lean module `KKGeneralEMDResidual.lean` proves the final residual-equivalence algebra for abstract components and \(q\ne0\). Lean has **not** proved that the geometric curvature computed from an arbitrary smooth KK metric satisfies the displayed block formula, nor the full general action reduction. Those geometric bridges require further formalization.

## 3. Single-centre Taub–NUT: explicit smooth Cartesian extension

For \(k>0,c\ge0\), let \(H=c+k/r\), angular period \(\psi\sim\psi+4\pi k\), set

\[r=\rho^2/(4k),\quad \chi=\psi/k\ (\mathrm{period}\ 4\pi),\quad \alpha=c/(4k^2),\quad q=1+\alpha\rho^2.\]

The Hopf map \(\mathbb C^2\setminus\{0\}\to(0,\infty)\times S^3\), using \(z_1=\rho\cos(\theta/2)e^{i(\chi+\varphi)/2}\), \(z_2=\rho\sin(\theta/2)e^{i(\chi-\varphi)/2}\), obeys

\[|d z_1|^2+|d z_2|^2=d\rho^2+\rho^2(d\theta^2+\sin^2\theta\,d\varphi^2+(d\chi+\cos\theta d\varphi)^2)/4.\]

Set real Cartesian coordinates \(X=(X_0,X_1,X_2,X_3)\) on \(\mathbb C^2\), \(s=|X|^2\), and

\[\omega=X_0 dX_1-X_1 dX_0+X_2 dX_3-X_3 dX_2.\]

The 4D *spatial* Taub–NUT metric becomes the exact, nonsingular tensor on all of \(\mathbb R^4\):

\[\boxed{g_{TN}=q\sum_{i=0}^3 dX_i^2-\frac{\alpha(2+\alpha s)}q\,\omega\otimes\omega,\qquad q=1+\alpha s.}\]

The verification script `tools/check_kk_nut_cartesian.py` checks all Hopf coefficient identities and the exact spherical-to-Cartesian equality (no limiting series). \(\omega\) is polynomial in \(X\); \(q\ge1\) for \(\alpha\ge0\), hence every component is smooth at \(X=0\), where \(g=\delta\). Because \(\omega\) corresponds to the vector \(JX\), with \(|JX|^2=s\), the four eigenvalues are \(q,q,q,1/q\), so the metric is strictly positive definite and \(\det g=q^2>0\). Adding \(-dt^2\) gives the smooth 5D Lorentzian product.

The period is essential: \(\chi\) has period \(4\pi\) to cover the Hopf 3-sphere once. Smaller quotient periods generally produce a lens-space/orbifold centre, not this smooth \(\mathbb R^4\) chart. The Python script checks coordinate algebra and the rank-one metric identities; **a Mathlib proof of the Hopf map as an atlas/diffeomorphism and of ContDiff for the full tensor is still missing.** The Lean module `KKNutCartesian.lean` verifies the rational rank-one eigenvalue, determinant and positivity certificates.

## Exact verification, boundaries and reproduction

Run (with `sympy==1.14.0`):

```
python -B tools/check_kk_gh_universal_2jet.py
python -B tools/check_kk_emd_universal_jets.py
python -B tools/check_kk_nut_cartesian.py
```

All three scripts have passed exact local execution. The dedicated CI compiles and axiom-audits three Lean modules with the repository-pinned Lean/Mathlib toolchain and preserves the exact source SHA. Passing this CI proves only the **Lean statements actually declared**, not all differential-geometric claims in this note.

Physics scope: classical, local, circle-invariant 5D vacuum Einstein gravity; no independent non-Abelian gauge sector, fermions, quantum theory, observed coupling constants or Standard Model reconstruction. Global nut extension is specifically the **one-centre** Taub–NUT case with the correct fibre period, not arbitrary harmonic singularities or multiple centres.

## References

- Dunajski & Gundry (2016), *Non-relativistic twistor theory and Newton–Cartan geometry*, sec. 3.1.2 (classical GH Ricci-flat theorem): https://www.damtp.cam.ac.uk/user/md327/DG_CMP_published.pdf
- Lotay et al., *Barriers for minimal submanifolds in Gibbons-Hawking ansatz*, New York J. Math. 28 (2022), sec. 2 (principal bundle, monopole equation, hyperkähler forms): https://nyjm.albany.edu/j/2022/28-34v.pdf
- Gibbons–Hawking/Taub–NUT construction lecture notes, Example 5.44: https://walpu.ski/Teaching/WS2324/DifferentialGeometry3/GaugeTheoryS.pdf
- Georgios Douzas, *The Kaluza–Klein reduction* (generic curvature jet formalism and scalar action): https://georgedouzas.github.io/posts/kaluza-klein-theories/part-iii-01-kaluza-klein-reduction.html
