# Polynomial E, WFS coordinates, Fenchel work and forgetting

2026-11-01. Additive proof module over verified PR #9,
without replacing the existing original E or any earlier proof source.

## Original object

The previous \`LinearInputVariablePairs.energy\` definition is

\[
E(x,y;u)=\lambda x^4/4+kx^2/2+ay^2/2-cxy-ux .
\]

Fix \(k,\lambda,a,c,y\), put \(V_y(x)=E(x,y;0)\), and define the
orientation-corrected gradient

\[
H_E(x,u)=(k x+\lambda x^3-cy-u,\ x)=(p,q).
\]

\`EnergyWfsFenchel.inc\` verifies that this is the earlier \`gradXu\`
with its second sign changed, and gives its explicit polynomial inverse
\((p,q)\mapsto (q,kq+\lambda q^3-cy-p)\).
The Jacobian +1 is an elementary derivative consequence of this formula.
This says nothing about arbitrary polynomial maps with determinant 1.

## Which diagram really commutes

For a fixed input \(u\) and the *physical* pairing \(ux\),

\[
u x-V_y(x)=(V_y'(q)-p)q-V_y(q)
\quad\text{on}\quad (p,q)=H_E(x,u).
\]

Consequently the sets of values at fixed \(u\), their bounded-above
properties, and their suprema under the boundedness hypothesis agree
exactly. The induced (p,q) domain is the curve
\(p=V_y'(q)-u\), not the full plane.

\`energy_min_iff_fenchel_max\` also proves the exact equivalence of
global E minima at fixed y,u and the corresponding Fenchel-work maxima.
No global minimizer existence or general lower semicontinuity is assumed.

## WFS is a coordinate change, not a license to change the pairing

The archived WFS family is \(G_p(r)=(r^p-1)/p\) for \(p\ne0\) and
\(G_0(r)=\log r\), on positive dimensionless intensity \(r\).
This supplement explicitly formalizes two members:

* \(G_0(r)=\log r\), with \(G_0(e^x)=x\);
* \(G_2(r)=(r^2-1)/2\), strictly one-to-one for \(r>0\),
  with inverse \(\sqrt{2z+1}\) on its positive-range branch.

The pulled-back physical pairing \(u G_2^{-1}(G_2(x))\) is identical
to \(ux\) on \(x\ge0\).

The **naive** pairing \(uG_2(x)\), however, changes the dual.
For \(V(x)=x^2/2\) and \(u=1\),

\[
G_2(x)-V(x)=-1/2 \quad (\text{all }x),\qquad
ux-V(x)\big|_{x=1}=+1/2.
\]

Thus a change of the linear pairing creates a genuinely different
conjugacy problem. The local map \(G_2\) is not injective across both
signs of x, so the positivity branch is essential.

## Forgetting and the dual: a precise obstruction

For any arbitrary potential \(V:\mathbb R\to\mathbb R\) and an
observation \(K:\mathbb R\to\beta\), suppose

\[
Kx=Ky \Longrightarrow ux-V(x)=uy-V(y)
\quad\text{for ALL }u\in\mathbb R.
\]

Using \(u=0\) and \(u=1\) gives \(x=y\): thus K is injective.
If K is an F0 idempotent retraction \(K^2=K\), injectivity forces
\(K=\mathrm{id}\).

This is a limitation on preserving every *pointwise* dual probe for
every input u. It does **not** prohibit a nontrivial quotient from
preserving the supremum for one fixed u, or from preserving only a
restricted observation family; those are separate, weaker claims.

## Nonconvex E and what ordinary convexification hides

The double well \(V(x)=(x^2-1)^2/4\) is an instance of the original
E (parameters \(k=-1,\lambda=1,a=1/2,c=0,y=1,u=0\)).

\(V(-1)=V(1)=0\), \(V(0)=1/4\), and \(V(x)\ge0\).
Every affine function \(mx+b\) below V everywhere satisfies \(b\le0\).
Therefore the supremum of affine minorants takes value 0 at x=0,
while the nonconvex potential has a barrier of height 1/4 there.
This is the precise obstruction behind loss of the barrier under
Fenchel biconjugation; no full general Fenchel–Moreau theorem is
claimed as a new Lean result in this supplement.

## Verification and remaining scope

- Lean proof module: \`linear_input/lean_check/EnergyWfsFenchel.inc\`.
- Exact Fraction witness tests: \`tools/check_energy_gauge_fenchel.py\`.
- Registered with \`tools/verify_main_result.py\` and \`tools/verify.py\`.
- Full verification: \`python -B -X utf8 tools/verify.py --proof-only\`,
  including \`--trust=0\` and public-declaration axiom audit.

Further unproved tasks: an arbitrary-p WFS smooth family, a genuinely
gauge-covariant convex dual framework on a nonaffine state manifold,
nontrivial dynamic state quotients preserving *restricted* Fenchel
outputs, and the concrete Laakso/Rule 481/Squares connections.
