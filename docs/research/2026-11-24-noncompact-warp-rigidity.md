# 2026-11-24 — Complete noncompact internal space does not evade the pure-vacuum warped-product obstruction

## Question and decision criterion

Can dropping compactness alone produce finite four-dimensional Einstein gravity and non-Abelian Killing-vector gauge bosons? Keep a smooth connected complete boundaryless Riemannian internal K, globally positive smooth warp e^A, exact 4D Minkowski external symmetry, metric g_D=g_K+e^{2A} eta_4, vacuum Ric_D=0, no independent fields, no branes or higher curvature terms. Fix finite positive higher-dimensional Newton constant. Test the ordinary finite kinetic coefficients, not just the existence of a symmetry algebra. Completeness refers to g_K.

## 1. Global rigidity, using a published theorem (not a new theorem of differential geometry)

The warped Ricci formulas, which follow from the mixed Christoffels Gamma^mu_(i nu)=A_i delta^mu_nu and Gamma^i_(mu nu)=-e^{2A}A^i eta_mu_nu, give
- internal: Ric_K=4(Hess A+dA tensor dA);
- external: Ric_mu nu=-e^{2A} eta_mu nu (Delta A+4 |dA|^2);
- mixed: zero.

With f=-4A, m=4, define Ric_f^4=Ric_K+Hess f-(df tensor df)/4, Delta_f f=Delta f-<df,df>. Both are zero by the two vacuum equations. The signs are independent of the external flat factor's signature. Thus all hypotheses of Jeffrey S. Case, *The nonexistence of quasi-Einstein metrics*, Pacific J. Math. 248 (2010), 277–284, Theorem 1.2, p. 278, hold with c1=c2=0. Its conclusion is that f is constant. No bound on A or its growth, and no finite-volume or compactness assumption is needed. Equivalently one may use the gradient estimate in Theorem 1.5 with zero right side of the drift equation. Consequently A is constant and Ric_K=0.

Source inspected 2026-11-24: https://doi.org/10.2140/pjm.2010.248.277 ; original https://msp.org/pjm/2010/248-2/pjm-v248-n2-p02-p.pdf ; preprint https://arxiv.org/abs/0902.2226 . This is an application of known rigidity, not a priority claim; the global analytic theorem is external, not Lean-verified here.

## 2. Finite kinetic norms

For an unwarped product after a constant external coordinate rescaling, the coefficient of R4 is Vol(K)/G_D; prior to rescaling the constant factor is e^{2A}. Complete connected noncompact Ricci-nonnegative Riemannian manifolds have infinite volume (Calabi–Yau minimal volume growth theorem; see C. Sormani, https://arxiv.org/abs/math/9903172). Thus ordinary four-dimensional Einstein gravity has a divergent kinetic coefficient. This statement is about the unmodified higher-dimensional Einstein-Hilbert action with finite fixed G_D.

For an internal Killing field X the ordinary KK metric-vector coefficient is proportional to its squared L2 norm integral |X|² dvol_K (inner-product matrix for multiple X). This is necessary for a normalizable zero mode, not sufficient for a consistent nonlinear truncation. For standard isometric reduction see J. Baptista, JHEP 05 (2024) 178, https://arxiv.org/abs/2306.01049 ; also the reduced curvature formula https://georgedouzas.github.io/posts/kaluza-klein-theories/part-iv-02-reduced-theory.html .

On Ricci-flat K, the Killing Bochner identity reads (1/2) Delta |X|²=|nabla X|². Choose a compactly supported Lipschitz radial cutoff chi_R, 1 on B_R, zero outside B_2R, |dchi_R|<=1/R; completeness makes its support compact. Weak integration by parts is valid by local smoothing, and yields
  I=integral chi_R² |nabla X|² <= 2 integral chi_R |dchi_R| |X| |nabla X|
  <= I/2 + 2 integral |dchi_R|² |X|².
So integral_B_R |nabla X|² <= 4 ||X||_2²/R². If X is L2, letting R grow forces nabla X=0 everywhere. Parallel fields have constant norm and pairwise commute by torsion-freeness. On the noncompact infinite-volume K a nonzero parallel field cannot be L2. Hence the space of normalizable Killing vectors is zero, even if noncompact K possesses a large non-Abelian isometry group. For compact K the same integration has chi=1 and gives commuting fields. This is the standard Bochner argument with cutoff, combined with the warped-product theorem; no novelty claim.

## 3. Independent exact witnesses (SymPy 1.14.0)

(a) Taub–NUT K with H=1+a/r, a>0, metric H(dr²+r² dOmega²)+H^-1(dpsi+a cos(theta)dphi)², fibre period 4pi a, previously tested in #199/#215. Determinant H² r⁴ sin²(theta). On the cutoff r<R the script integrates directly:
- volume = 16 pi² a (R³/3+a R²/2);
- norm squared integral of fibre generator partial_psi = 16 pi² a R³/3;
- axial rotation norm squared integral is at least (32 pi² a/3)(R⁵/5+a R⁴/2+a² R³/3); the symmetric-coordinate lift adds a²/3 times the fibre integral. The lower bound comes from the base rotation and is independent of its vertical lift.

All diverge. This does not conflict with the actual 5D KK monopole in #199 (Taub–NUT is then part of physical spacetime, not an internal space integrated out) or with its non-Abelian tangent holonomy in #185. A holonomy algebra is not automatically a finite kinetic-norm dynamical 4D gauge sector.

(b) A sharpness test when completeness is dropped: the smooth local 6D metric on r>0
  ds²=dr²+r^(4/5) eta_4+r^(-6/5) dpsi²
has nonconstant A=(2/5)log r. It is the spacelike Kasner power-law ansatz with four exponents p=2/5 and one q=-3/5, 4p+q=4p²+q²=1. The independent script constructs all Christoffels and Riemann components and verifies all 36 Ricci entries zero, the two-dimensional weighted Ricci and drift equations zero, and Kretschmann = 768/(125 r⁴) by both tensor contraction and a separate exponent sum. The radial path has finite length to r=0, and scalar curvature invariant diverges there; it is not a smooth complete internal metric and does not defeat the theorem. No independent matter introduced.

Reproduce: python -m pip install sympy==1.14.0 ; python tools/check_noncompact_killing_norm.py . Local run 2026-11-24 PASS: determinant, exact three integrals and limits, cutoff square identity, all 36 Ricci components, Kretschmann, two weighted residuals. Local script SHA256 e73987f55a3adba87d38b6882ef522c9886969b3d426ea56eea1e81f303a5355. Script commit 504a18a9dd9f82fa59a62883653f73592d2969bb. No new Lean kernel theorem in this PR; local Lean executable unavailable. The global proof depends on the cited analytic theorems, not the finite oracle. First trial of independent curvature contraction caught a factor-of-two error in the anticipated invariant; corrected using the separately derived exponent sum and re-ran PASS.

## 4. Research ledger at 2026-11-24

Latest heads checked against Actions (PR-triggered run listing; not an exhaustive historical audit):
- #176 ba1dc78f9be0ca3867fcaeb5b51dde01687c3ff2 dedicated 44952037270, 44952037252 action_required.
- #177 8a84ab5a623150c1dc2df6f8614e4b5f0df7d485 dedicated 44953750468 action_required.
- #178 5ce3ddc293417ffea43c79b99b16e36ff1594186 dedicated 44954103336 action_required.
- #179 cb0549a92dc2d7297093196788d6936f21418098 dedicated 44955089236 action_required.
- #183 8a6ffd4b9d91a5e3f41238da841b2a64b70a846c only three head runs returned, all action_required (integration 44958061416); no dedicated run returned on this head. All five last commits contain generated graph artifacts only. No compiler failure is established by action_required; no speculative source fix. Earlier exact source SHAs/axiom logs for these five were not recovered.
- #221 independent passive-gel audit 121da387b03c96373fb7863f4ba48f1e4c139ed7: dedicated 45111361398 and integration 45111361326 SUCCESS. This is Python evidence, not the #183 Lean audit.
- #199 earlier exact source 6b20543fe39ef831669b45a2de48ea2f5581ad61 dedicated 45024281638 SUCCESS, integration 45024281565 and compressed reachability 45024281609 FAILURE. No claim of complete integration.
- #238 exact head 53d7604798fd6f3907d700a3f730a9be32eff6a8 dedicated 45134693108 SUCCESS, including theorem axiom audit (8 Lean theorems; Hopf transition winding -1, not general Chern-class formalization).
- #242 prior verified source d0ce0eb04249d483e8193075f761a51a637300d0 dedicated 45141607885 SUCCESS, integration 45141607738 FAILURE at all-standalone-modules audit. It is finite coordinate curvature, not unrestricted manifold curvature; do not confuse dedicated CI with integrated verification.
- #214 previous source 119a9d0a3703597392e4c8497469befb367af8fe dedicated 45091101730 and integration 45091101665 SUCCESS (previously confirmed); generated successor c5873d5aeb5c5191c600b0977a329f8edf9d2c30 still action_required. Effective-medium branch remains separate.

## 5. Decision and next one bounded problem

Complete noncompact, positive-warp, flat external, block diagonal pure vacuum route is closed for finite ordinary 4D kinetic norms. This does not exclude incomplete internal metrics with admissible completions, curved/time-dependent external geometry, non-isometric modes, nonproduct backgrounds, or altered actions. The 4D Lorentz symmetry is exact at the ansatz level, but no chiral matter, quantum theory, observed couplings or equivalence-principle test is derived. The gel branch has extra relaxation/site variables and must not be described as pure gravity.

Next: test the exact pure-vacuum Einstein external curved (negative Einstein constant) warped ansatz using Case's nonpositive-fibre theorem and explicitly classify which assumptions still fail; alternatively if that route is closed, select a nonproduct metric with well-defined finite perturbation kinetic coefficients. Do not merely introduce independent matter or boundary conditions to force a desired result. Keep all work draft; no main merge.
