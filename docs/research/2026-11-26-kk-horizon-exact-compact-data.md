# 2026-11-26 — Compact exact vacuum data with nonlinear curvature blow-up and a surviving regular horizon patch

## Result (finite task)

On the **original** H^3 x S^1 initial slice of #270, there exist arbitrarily small, smooth, compactly supported perturbations of the vacuum initial data, with no extra matter or change of topology, whose maximal globally hyperbolic vacuum development contains a timelike geodesic reaching unbounded scalar curvature in finite proper time. This connects the finite-global-norm and nonlinear blow-up gates in #275–#278 for a particular zero-circle-mode family. The same construction leaves a distant exterior patch exactly isometric to the original geometry all the way to its smooth chronology horizon. Thus local nonlinear instability does not establish universal chronology protection. No claim of genericity or of global C^2-inextendibility of the entire development.

## 1. Exact compact perturbation without a conformal tail

Fix beta>0, s=sqrt(beta), r0>s, f=1-beta/r^2, f0=f(r0). On the exterior of #270 use coordinates chi=v-r*(r), r*'=1/f; the metric is -dr^2/f+f dchi^2+r^2 gamma, where gamma is the unit H^3 metric and chi has the original period L. On Sigma={r=r0}, let c=f0 dchi^2 and h=r0^2 gamma. The spatial metric is g0=c+h. Use K=+1/2 Lie_n g0, with n=sqrt(f0) partial_r at fixed chi. The background second fundamental form is
    K0=b c+a h,
    a=sqrt(f0)/r0>0, b=f'(r0)/(2sqrt(f0))>0.
R(g0)=-6/r0^2 and a(a+b)=1/r0^2. Both vacuum constraints hold.

Let T be a smooth compactly supported symmetric TT covariant tensor on (H^3,h), pulled back independently of chi and zero on circle indices. By the explicit fourth-order differential operator and conformal transform in #275, choose T=r0^2 W, where W equals z^-2 diag(1,-1,0) on an arbitrarily large closed hyperbolic ball about X0. Then the h-endomorphism of T there has eigenvalues (1,-1,0). Briefly, in the upper half-space choose a smooth compact cutoff identically 1 on a neighborhood of the ball, apply P_ik P_jl A_kl-(1/2)P_ij P_kl A_kl to A=cutoff*(z log(z)/2)*diag(1,-1,0), P=delta Delta_E-partial partial, and multiply by z and r0^2. The resulting tensor is smooth, compact, symmetric, divergence-free and trace-free; the local fourth derivative is z^-3. This is not mere cutoff multiplication of a TT tensor.

Let Q=|T|_g0^2 >=0. For sufficiently small real epsilon choose
    delta(x) = (b-sqrt(b^2-(2/3)epsilon^2 Q(x)))/2,
    g_epsilon = g0,
    K_epsilon = (b-2delta)c+(a+delta)h+epsilon T.
Require (2/3)epsilon^2 sup Q < b^2, so the root is uniformly positive. No elliptic solve, matter, or independent scalar field is introduced; delta is a pointwise algebraic function of the chosen gravitational seed. Unlike #278, the trace is not held constant.

**Momentum constraint:** the product connection preserves c,h; because delta is independent of chi, div(delta c)=0 and div(delta h)=d delta. The trace of K_epsilon is 3a+b+delta, and div T=0, hence div K_epsilon-d tr K_epsilon=0 exactly, all four components.

**Hamiltonian constraint:** tr T=0 and T is orthogonal to c,h. Thus
    R(g0)+(tr K_epsilon)^2-|K_epsilon|^2
      = -6/r0^2 + 6a(a+b) + 6(b delta-delta^2)-epsilon^2 Q = 0.
The last equality is exactly the square-root equation. The oracle computes the trace, momentum and Hamiltonian formula directly in product coordinates with arbitrary symmetric H^3 tensor components and arbitrary delta(x,y,z), and then the root identities. It is not a linearized constraint check.

Outside supp T, delta=0 and both initial tensors coincide exactly with background. The square-root expression is smooth on the chosen interval and delta=epsilon^2 Q/[3(b+sqrt(b^2-(2/3)epsilon^2 Q))]=O(epsilon^2) in every fixed finite Sobolev norm; the compact support stays fixed. (The rationalized denominator expression follows from delta*(b+sqrt(...))=epsilon^2 Q/3.) Therefore for each fixed m, ||K_epsilon-K0||_H^m=O(|epsilon|), and the metric difference is identically zero. For instance E_m=||K_epsilon-K0||_H^m^2 is a finite positive initial perturbation norm of order epsilon^2. No conserved canonical energy, ADM mass, or finite total background energy is asserted.

## 2. Match to an exact anisotropic interior

On the ball T has constant orthonormal eigenvalues, Q=2, and delta is constant delta_in. Put N0=r0^3 sqrt(f0), D=beta=N0 b, B=N0(b-2delta_in)>0, P=N0 epsilon. Then
    D^2=B^2+4P^2/3,
    N0(2(a+delta_in)+(b-2delta_in))=N0(2a+b).
Thus the first integral D and initial logarithmic volume combination are unchanged. At epsilon!=0, D>B>0 and D>|P|.

Use the #277 exact Bianchi V x circle family with time tau=0 on Sigma and tau<0 to the past:
    q0=sqrt(f0), q=q0 exp(D tau), E=exp(w)=D q/(1-q^2),
    C=log(q0)+B tau, p=P tau, A=(w-C)/2, N=exp(3A+C),
    g=-N^2 d tau^2+exp(2C)d chi^2+
        exp(2A)z^-2[exp(2p)dx^2+exp(-2p)dy^2+dz^2].
At tau=0: E0=r0^2 q0, exp(A)=r0, exp(C)=q0, p=0 and N=N0. Also w'=D(1+q^2)/(1-q^2), so w'(0)=N0(2a+b). The second fundamental form eigenvalues on the initial slice are exactly b-2delta_in, a+delta_in+epsilon, a+delta_in-epsilon, a+delta_in. Therefore both induced metric and K match the compact data on the ball, not just their first variations. For epsilon=0 this is the original exterior with f=q^2, r^2=beta/(1-q^2). For epsilon!=0 it is an exact Ricci-flat metric by #277's full nonlinear Ricci identity, C''=p''=0, w''=4 exp(2w), and (w')^2-4 exp(2w)=D^2. Constants and time shift do not alter that computation. #277's exact Python tensor oracle and Lean algebra audit CI both succeeded.

## 3. Finite causal reach protects the entire singular trajectory

It is essential to check that the nonlinear causal cone does not outgrow the matching ball. For every causal curve of this anisotropic solution, using tau as time,
    |dX/dtau|_gamma <= exp(2A+C) exp(|p|)=E exp(|P tau|).
For tau<=0,
    E/E0 = exp(D tau)(1-q0^2)/(1-q0^2 exp(2D tau)) <= exp(D tau).
Consequently the total hyperbolic displacement to the initial slice is bounded by
    integral_(-infinity)^0 E exp(|P tau|) d tau <= E0/(D-|P|).
Choose once and for all R>2E0/D and restrict |P|<=D/2, in addition to the square-root condition after choosing T. This avoids any circular dependence of the ball on the small parameter. The ball with the full circle has compact closure in Sigma. At every finite tau<=0 the causal footprint of the central comoving timelike curve X=X0, chi fixed, lies strictly in that ball; the margin also protects an open neighborhood. On any closed time interval the homogeneous spatial metrics are uniformly comparable to the complete product spatial metric; bounded causal speeds imply that the homogeneous solution has Cauchy slices. The full periodic circle is included in the matched region, so winding causes no loophole.

Apply standard geometric local uniqueness and the domain-of-dependence property for the vacuum Einstein Cauchy problem (smooth data, here four spatial dimensions). The globally hyperbolic development of the open matched ball times S^1 is represented by the interior of its domain of dependence in the homogeneous solution; its protected portion embeds isometrically into the maximal globally hyperbolic development of the full compactly perturbed data, by the local Cauchy development/gluing property. This is a locality argument for the *nonlinear* equation, not a perturbation expansion or a claim of solving the inhomogeneous metric globally. No finite cutoff-time limit is exchanged with epsilon.

## 4. Curvature of the actual development

For each fixed nonzero sufficiently small epsilon, let M=(3D-B)/2>0 and t=integral_(-infinity)^tau N(u)du. From q~exp(D tau), N~const exp(M tau), t~N/M; the protected central comoving timelike geodesic reaches t=0 in finite proper time. Define k_i=(B,(D-B)/2+P,(D-B)/2-P,(D-B)/2)/M in (chi,x,y,z) order. The vacuum relation gives sum k_i=1 and sum k_i^2=1. By #277's orthonormal Riemann computation and asymptotics (including negative mixed Lorentzian contractions),
    lim_(t->0+) t^4 R_abcd R^abcd
       = Kstar = 4 sum_i k_i^2(k_i-1)^2+4 sum_(i<j) k_i^2 k_j^2
       >= 4 k_z^2 (1-k_z)^2 > 0,
since k_z=(D-B)/(3D-B) lies strictly between 0 and 1. The constants C(0), q0 and p(0) do not affect the limiting exponents. The matched solution has curvature blow-up for fixed nonzero epsilon, along a geodesic in the exact development. In particular that curve cannot terminate at a regular C^2 Lorentzian extension point. This is the sought connection of global finite-norm small exact data and fully nonlinear local curvature divergence.

## 5. Important counterweight: the distant horizon survives locally

Because the seed and correction have compact support, a sufficiently distant ball in H^3 disjoint from that support has exactly original data. Choose its radius larger than the original causal reach acosh(r0/s), including the entire circle. The same nonlinear domain-of-dependence argument, using the original exact metric, gives a distant open patch extending to all r>s down to r=s in the development. In the original (r,v) chart the metric of this patch has its known smooth vacuum continuation through r=s, with periodic v and closed timelike circles for r<s. This proves local extendibility of that patch as a metric and coexistence of a singular region with a locally regular candidate chronology horizon. It does **not** by itself prove a Hausdorff global extension of the whole maximal development or global persistence of chronology violation, and does not settle any universal causality selection. The maximal globally hyperbolic development itself has no closed causal curves by definition; the question is what extensions beyond it can be admitted.

## 6. Evidence, literature, limits, next gate

SymPy 1.14.0 local exact script ran successfully in all five check groups; SHA256 b70bc577a9a8f14b081f4c2b764b219bdd00713c5427ce7e2cf5174cac986db1, Git blob 1252e7ed4b24f2497e1d22451a42305252c32746. Reproduce python -B tools/check_kk_horizon_exact_localization.py. The full nonlinear curvature calculation is reused from #277, TT construction from #275; both dedicated Python CIs passed. The analytic Cauchy existence/uniqueness and finite propagation, integrations and limits are hand arguments; Lean candidates cover only elementary algebra, not the PDE theorem. No numerical PDE solve or new all-component spacetime Ricci computation for the inhomogeneous exterior is claimed. No general gluing theorem (which may require absence of Killing initial data) is used; explicit product constraints bypass that hypothesis for this restricted seed family. Related literature: Denaro and Dotti, Strong cosmic censorship and Misner spacetime, https://arxiv.org/abs/1505.01092; Halpern, Exact solutions of five dimensional anisotropic cosmologies, https://doi.org/10.1103/PhysRevD.66.027503; Chrusciel, Isenberg and Pollack, Initial data engineering, https://arxiv.org/abs/gr-qc/0403066; Hintz, Gluing Small Black Holes into Initial Data Sets, https://doi.org/10.1007/s00220-024-04989-6; Einstein Cauchy problem overview by Rendall, https://pmc.ncbi.nlm.nih.gov/articles/PMC5256071/. This is an explicit construction for our background, not a claim of priority for general gluing or chronology-protection theory.

Predecessor heads and runs checked in this iteration:
- #275 755d6fac1dc0c6911d06973a247e0decc184511c, 45717853208 success (Python).
- #277 c567ff3e849758f8c8ad80d385522e330d40f623, 45718430742 success (Python, Lean 5 algebraic statements and axiom audit).
- #278 70ac8464b16ea68a2ae37e1440b0cfce275e20a4, 45718804561 success (Python).
Other older branches not re-audited in this bounded manual continuation; their previous action_required blockers are not certified resolved.

A: PASS for arbitrarily small globally finite Sobolev perturbation norms of smooth exact compact vacuum data; no invariant conserved energy claim.
B: PASS for actual finite-proper-time local scalar curvature blow-up of these same data in the full nonlinear vacuum Cauchy development. OPEN for genericity, nonzero-circle-frequency nonlinear lift, weak regularity, entire development C^2-inextendibility.
C: PARTIAL, with a limitation: local chronology horizon can become singular but distant regular local extension patches survive. Next finite task: study whether the regular distant patch can be attached as a Hausdorff vacuum extension of the full development with a closed timelike curve, or prove an obstruction; distinguish global chronology from local C^2 singularity. Keep the other high-dimensional and gel branches separate. Draft only, no main merge.
