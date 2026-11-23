# Siphon E/L: topological obstruction to three tangent-probability reads, and regularity of four

Date: 2026-11-23. Independent follow-up to PR #240. The topology statements are **paper proofs**; the stand-alone Lean module certifies only the explicitly listed algebraic nonvanishing statement if its exact-head CI succeeds. No generic manifold-recovery theorem is claimed.

## Setup

Use the existing automorphisms
\[
I(u,v)=v+u^3,\quad
E(u,v)=(u+I(u,v)^2,\ I(u,v)-(u+I(u,v)^2)^3),\quad
L(u,v)=(v,v-u).
\]
For a finite operation word \(w\) over \(\{E,L\}\), let \(q_w(u,v)=(w(u,v))_1\), applying the letters in sequence. Its probability read is
\[
P_w(u,v)=\frac{1}{1+9q_w(u,v)^4}.
\]
It contains **exactly the same information** as \(q_w(u,v)^2\), since \(s\mapsto1/(1+9s^2)\) is strictly decreasing for \(s\ge0\). All words fix the origin, and \(D E(0)=\mathrm{id}\). The linearization of \(L\) satisfies \(L^3=-\mathrm{id}\), \(L^6=\mathrm{id}\), so \(Dq_w(0)\) is up to sign one of the three linear forms \(du,dv,d(v-u)\), determined by the number of \(L\)'s modulo 3.

## Theorem A: three observations with two independent linear parts fail locally

**Statement.** Let \(q_1,q_2,q_3\) be \(C^1\) real scalar functions near \(0\in\mathbb R^2\), all vanishing at 0, and suppose the gradients of \(q_1,q_2\) there are linearly independent. For any continuous **even** sensor \(h:\mathbb R\to\mathbb R\), the map
\[
z\mapsto(h(q_1(z)),h(q_2(z)),h(q_3(z)))
\]
is not injective on *any* neighborhood of 0.

**Proof.** By the inverse function theorem, the coordinate map \(\theta=(q_1,q_2)\) is a local diffeomorphism with \(\theta(0)=0\). Choose a small circle \(C_\varepsilon\) inside its coordinate image. For \(x\in C_\varepsilon\), the distinct states \(z_+(x)=\theta^{-1}(x)\) and \(z_-(x)=\theta^{-1}(-x)\) have identical first two readings by evenness. The third-read difference
\[
g(x)=h(q_3(z_+(x)))-h(q_3(z_-(x)))
\]
is continuous and satisfies \(g(-x)=-g(x)\). Joining any point on the circle to its antipode along a semicircle, the intermediate value theorem supplies a zero of \(g\). Both states can be taken arbitrarily close to the origin. QED.

**E/L consequence.** If a triple of words has **two different counts of \(L\) modulo 3**, its gradients include two independent directions. Thus **every such three-word probability protocol fails**, regardless of the length/complexity of the words.

The only globally injective triple candidates are those whose three words have the same number of \(L\)'s modulo 3. This is a necessary condition, not a claim that such a triple works.

## Theorem B: any three-read protocol containing two pure E-iterates fails

**Statement.** For any \(m,n\in\mathbb N\), and any finite word \(w\) over \(E,L\), the protocol
\[
z\mapsto(P_{E^m}(z),P_{E^n}(z),P_w(z))
\]
is never injective on any neighborhood of 0. This includes the identity as \(E^0\).

**Proof.** Work in polynomial coordinates \((u,r)\), \(r=v+u^3\). For every \(k\), \(q_{E^k}(u,r)=u+kr^2\), invariant under \(r\mapsto-r\).

If the number of \(L\)'s in \(w\) is nonzero modulo 3, the pair \(q_{E^m},q_w\) has linearly independent gradients at the origin; Theorem A applies.

Otherwise \(Dq_w(0)\) is \(\pm du\), so in \((u,r)\) coordinates the function
\[
H(u,r)=q_w(u,r)+q_w(u,-r)
\]
satisfies \(H(0,0)=0\) and \(\partial_uH(0,0)=\pm2\ne0\). The implicit function theorem gives a small graph \(u=\alpha(r)\), with \(H(\alpha(r),r)=0\). For every sufficiently small \(r\ne0\), the distinct points \((\alpha(r),r)\) and \((\alpha(r),-r)\) have identical E-iterate squared reads, and their \(w\)-reads are opposite, hence have equal probabilities. QED.

## A misleading finite-grid success with a real collision

Consider the triple \(\{\mathrm{id},E,L E L L\}\). All three words have the same \(L\)-count modulo 3, so Theorem A alone does not apply. Exact rational tests show that this triple distinguishes every state in each of the **49-, 169-, 441-, and 841-point** regular grids tested.

Yet it **fails globally** by Theorem B. An explicit intermediate-value bracket makes the failure checkable without relying on a generic implicit-function theorem.

Fix \(r=1/100\). Write \(z_\pm(u)=(u,\pm r-u^3)\). Their first two readings agree **for every** \(u\). Let
\[
H(u)=q_{LELL}(z_+(u))+q_{LELL}(z_-(u)).
\]
Exact rational arithmetic verifies
\[
H(-1/1000)>0,\qquad H(0)<0.
\]
By the intermediate value theorem there is \(u_*\in(-1/1000,0)\) such that \(H(u_*)=0\). The third first-coordinate readings are then opposite, so the three probabilities match at two **distinct real states** \(z_\pm(u_*)\), with vertical distance \(2r=1/50\). Numerically \(u_*\approx-0.000100060035\), not a claim that the root is rational.

This is a concrete warning: finite exact grids may all appear injective even when a continuous real-state collision is rigorously guaranteed.

## Theorem C: the certified four-read map is a smooth embedding off the origin

PR #240 proves, with pinned-Lean kernel verification, that
\[
\Phi_4(u,v)=\big(P_{\mathrm{id}},P_E,P_L,P_{E\circ L}\big)(u,v)
\]
is injective for all real \((u,v)\).

Its derivative has rank **two at every nonzero state**, and rank **zero at the origin**. For the algebraically equivalent *squared-coordinate* map
\[
F(u,v)=\big(u^2,\ (u+r^2)^2,\ v^2,\ (v+t^2)^2\big),\qquad
r=v+u^3,\quad t=v-u+v^3,
\]
four \(2\times2\) minors of \(DF\) are
\[
M_{13}=4uv,\quad
M_{12}=8ur(u+r^2),\quad
M_{23}=4v(u+r^2)(1+6u^2r),
\]
\[
M_{14}=4u(v+t^2)(1+2t(1+3v^2)).
\]

At \(u v\ne0\), \(M_{13}\ne0\).
At \(u=0,v\ne0\), \(M_{23}=4v^3\ne0\).
At \(v=0,u\ne0\), \(M_{12}=8u^4(u+u^6)\). If it vanishes, \(u+u^6=0\), which forces \(u<0\); then \(M_{14}=4u^3(1-2u)\ne0\).

Thus some minor is nonzero at every nonzero state. The coordinate probability is the smooth function \(\rho(s)=1/(1+9s^2)\) of squared coordinate \(s\ge0\). Whenever an \(F\)-row is nonzero its squared reading \(s\) is positive, so \(\rho'(s)=-18s/(1+9s^2)^2\ne0\). Therefore the probability map \(\Phi_4\) has the same differential rank. All word first coordinates vanish at 0, and \(\rho'(0)=0\), so \(D\Phi_4(0)=0\).

The map \(\Phi_4\) is a **topological embedding globally**: if \(\Phi_4(z_k)\to\Phi_4(z)\), the identity and \(L\) readings bound \(|u_k|\) and \(|v_k|\), so all subsequential limits are finite; continuity and injectivity force every limit to equal \(z\). The inverse on the image is therefore continuous. Off the origin, the constant-rank theorem makes it a smooth embedding, and on each fixed compact subset \(K\subset\mathbb R^2\setminus\{0\}\) there are \(c_K,C_K>0\) with
\[
c_K\|z-w\|\le\|\Phi_4(z)-\Phi_4(w)\|\le C_K\|z-w\|,\quad z,w\in K.
\]
The positive lower constant follows from a uniform local lower bound near the diagonal and compactness off the diagonal, not from a global inverse Lipschitz claim. Near the origin the inverse is not locally Lipschitz (PR #237).

The accompanying Lean module checks the algebraic assertion that **not all four displayed minors can vanish at a nonzero real point**. The rank/differential and topological arguments above remain *paper proofs* unless separately formalized.

## Current minimum and open case

For **all** fixed E/L-word protocols using the specified tangent probability sensor,
\[
\boxed{3\le N_{\min}\le 4}
\]
remains the unconditional bound. We have excluded all three-word protocols with mixed \(L\)-counts modulo 3, and all protocols containing two pure E-iterates. The remaining same-residue triples without this structure have not been classified. Neither exact finite-grid separation nor Lean verification of four-read sufficiency alone answers their global injectivity.

This is related to real phase retrieval in the sense of absolute-value measurements, but the nonlinear word observations and exact-state target differ from standard linear phase retrieval modulo global sign.

## Verification

Run:
\`\`\`sh
python3 -B -m unittest discover -s tests -p 'test_siphon_three_probe_obstructions.py' -v
python3 -B tools/verify_toolchain_modules.py --module Research.SiphonFourProbeRegularity
\`\`\`
The Python suite uses exact Fractions and dual numbers to check 4 minor identities, 6^? finite E/L linearizations, IVT endpoint signs, rank on rational grids, and the deceptive-grid example. Exact-head CI status and axiom audit must be checked independently.
