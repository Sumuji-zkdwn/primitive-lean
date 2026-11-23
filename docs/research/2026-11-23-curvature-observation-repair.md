# A curvature-probability sensor repairs local observability at the common fixed point

Date: 2026-11-23. Companion to PR #237. This is an **explicit local construction** rather than a proof of generic manifold recovery. The analytic estimates are paper proofs; the regression check is finite.

## Why changing the sensor matters

The original tangent-minor sensor in PR #232 is \(h(u)=1/(1+9u^4)\). Its derivative at the origin vanishes. PR #237 shows that no **finite** family of \(E,L\) operation words can make an immersion at the origin when every read uses this exact sensor. The obstruction is due to the sensor, not merely the number of operations.

We can change the observable to a higher-order geometric quantity without changing the dynamical maps. The invariant level curve \(I(u,v)=r\) is \(v=r-u^3\), parametrized by increasing \(u\). Its **signed Euclidean curvature** is

\[
\kappa(u)=\frac{-6u}{(1+9u^4)^{3/2}}.
\]

Define the bounded probability-value sensor

\[
q(u)=\frac12+\frac{\kappa(u)}{12}
     =\frac12-\frac{u}{2(1+9u^4)^{3/2}}.
\]

For all real \(u\), \(0<q(u)<1\). Indeed, \(|\kappa(u)|<6\): for \(|u|\le1\), bound the numerator by 6 and use the positive denominator; for \(|u|\ge1\), use \((1+9u^4)^{3/2}\ge27|u|^6\).

The same linear map \(L(u,v)=(v,v-u)\) supplies the second coordinate as its first read. Thus two curvature probabilities give

\[
\Psi(u,v)=\big(q(u),q(v)\big)
         =\big(q((u,v)_1),q((L(u,v))_1)\big).
\]

## Theorem: explicit local bi-Lipschitz reconstruction

On the square \(K=[-1/4,1/4]^2\), for every \(z,w\in K\),

\[
\boxed{\frac13\|z-w\|_2\le\|\Psi(z)-\Psi(w)\|_2
\le\frac12\|z-w\|_2.}
\]

**Proof.** Differentiate:

\[
q'(u)=\frac{45u^4-1}{2(1+9u^4)^{5/2}}.
\]

If \(|u|\le1/4\), then \(45u^4\le45/256\) and \(1+9u^4\le265/256\). Therefore \(q'\) is negative and

\[
|q'(u)|\ge
\frac{211/256}{2(265/256)^3}
=\frac{6914048}{18609625}>\frac13;
\qquad |q'(u)|\le\frac12.
\]

The scalar mean-value theorem gives \( (1/3)|a-b|\le|q(a)-q(b)|\le(1/2)|a-b|\) for any \(a,b\in[-1/4,1/4]\). Apply this to both input coordinates and sum squares. QED.

In particular, \(D\Psi(0,0)=\mathrm{diag}(-1/2,-1/2)\): a full-rank origin is possible once **second-order curve geometry** is observable. Compared to the old sensor, the inverse is Lipschitz on the displayed patch with an explicit noise-amplification bound of 3.

## What this result does and does not establish

- It **does** give a probability-valued, curvature-derived, locally stable two-probe observation system, with quantitative constants and the same \(E,L\) model.
- It **does not** give global injectivity. The curvature function is not monotone on all of \(\mathbb R\); its derivative changes sign at \(|u|=45^{-1/4}\).
- A signed curvature requires a choice of Euclidean metric and orientation of the curve; this is more geometric than an arbitrary coordinate value but is **not** invariant under every change of coordinates.
- The two measurements in this construction use \(\mathrm{id}\) and \(L\), not \(E\). The role of \(E\) remains to provide the invariant foliation and dynamics. The construction proves **existence of a remedy**, not that E/L dynamics alone supplied new information.
- On a real physical data manifold the relevant second-jet/curvature sensor may be unavailable or noisy. No claim is made about such deployment.

Independent test: \`python3 -B -m unittest discover -s tests -p 'test_siphon_curvature_sensor.py' -v\`. The test checks rational derivative lower bounds and floating evaluation of the curvature formula; the proof above is the source of the global/local assertions.
