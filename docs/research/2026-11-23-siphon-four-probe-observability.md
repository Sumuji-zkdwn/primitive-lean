# Four tangent-probability observations suffice for the siphon maps

Date: 2026-11-23. Standalone improvement of PR #232/#237. **Global real-algebraic paper proof** and exact finite tests. No change to the previously defined E, L or the invariant. A separate Lean certificate is required before calling the new four-probe theorem kernel checked.

## Objects and exact theorem

For \((u,v)\in\mathbb R^2\), let

\[
I(u,v)=v+u^3,\quad
E(u,v)=(u+I(u,v)^2,\ I(u,v)-(u+I(u,v)^2)^3),
\quad L(u,v)=(v,v-u).
\]

For the tangent of the invariant cubic, the first squared-minor probability is

\[
p(u,v)=\frac{1}{1+9u^4}.
\]

Let \(Q(z)=(p(z),p(Ez),p(Lz),p(E(Lz)))\), where \(E(Lz)\) means **first apply L, then E**.

**Theorem:** \(Q:\mathbb R^2\to(0,1]^4\) is injective.

Each scalar probability reading \(p(z)\) is equivalent to the squared first-coordinate reading \(z_1^2\), because
\[
p(z)=\frac{1}{1+9(z_1^2)^2}
\]
is injective as a function of \((z_1)^2\ge0\).

Thus suppose \(z=(u,v)\) and \(w=(x,y)\) have the same four readings. The first and third give \(u^2=x^2\) and \(v^2=y^2\), so \(w\) is one of the four sign choices \((u,v)\), \((-u,v)\), \((u,-v)\), \((-u,-v)\). We rule out the last three unless they coincide with \(z\).

Write
\[
r=v+u^3,\qquad t=v-u+v^3.
\]
Define \(B(u,v)=(u+r^2)^2\) and \(D(u,v)=(v+t^2)^2\). These are precisely the squares of the first coordinates after \(E\) and after \(E\circ L\).

### Opposite sign in both coordinates: (-u,-v)

\[
B(u,v)-B(-u,-v)=4ur^2,\qquad
D(u,v)-D(-u,-v)=4vt^2.
\]

If \(u\ne0\) and \(r\ne0\), the first difference is nonzero. If \(u=0\), \(v\ne0\), then \(t=v+v^3=v(1+v^2)\ne0\), so the second is nonzero. If \(r=0\), \(u\ne0\), then \(v=-u^3\ne0\) and \(t=-u(1+u^2+u^8)\ne0\), so the second is nonzero. The remaining case is the origin, where both states coincide.

### Flip the first coordinate only: (-u,v)

There is nothing to show if \(u=0\). Otherwise the exact factor identities are

\[
B(u,v)-B(-u,v)=4u(u^6+v^2)(1+2u^2v),
\]
\[
D(u,v)-D(-u,v)=-8uv(1+v^2)\big(u^2+v+(v+v^3)^2\big).
\]

The first difference can vanish only if \(1+2u^2v=0\), hence \(v=-1/(2u^2)<0\). Put \(a=u^2>0\). Then

\[
u^2+v+(v+v^3)^2
\ge a-\frac1{2a}+\frac1{4a^2}
=\frac{4a^3-2a+1}{4a^2}>0.
\]

The last strict inequality follows from the explicit sum-of-squares decomposition

\[
4a^3-2a+1=(2a-1)^2+2a\big((a-1)^2+a^2\big)>0.
\]

Since \(u\ne0\), \(v\ne0\), and \(1+v^2>0\), the second difference must therefore be nonzero.

### Flip the second coordinate only: (u,-v)

There is nothing to prove if \(v=0\). Otherwise

\[
B(u,v)-B(u,-v)=8u^3v(u^6+u+v^2),
\]
\[
D(u,v)-D(u,-v)
=-4v\big(2u(1+v^2)-1\big)\big(u^2+(v+v^3)^2\big).
\]

Because \(v\ne0\), the final factor \(u^2+(v+v^3)^2\) is strictly positive. If \(D\) is equal for both states, necessarily
\[
u=\frac1{2(1+v^2)}>0.
\]
But then every factor in the first difference, except the nonzero signed \(v\), is strictly positive, so \(B\) cannot be equal.

These three cases exhaust the possible signs. Therefore the **four-probe probability signature is injective on all real states**.

## Minimum probe count

For the same probability sensor \(p\), **two scalar readings can never identify all of \(\mathbb R^2\)** when composed with any finite words from the origin-fixing maps E and L. The two-output observation map would be a continuous injective map from \(\mathbb R^2\) to \(\mathbb R^2\), so invariance of domain would force its image open. But all probabilities lie in \((0,1]\), and every reading equals \(1\) at the origin; the image contains the boundary point \((1,1)\), so it cannot be open. Thus
\[
\boxed{3\le N_{\min}\le4.}
\]

This is an exact bound for the **specified fixed-word, scalar tangent-probability sensor family**. Three-read sufficiency or impossibility has NOT been proved.

Three of the four particular reads can fail:
* id, E, L: the nonzero states \((u,-u^3)\) and \((-u,u^3)\) have equal readings.
* id, L, E∘L: \((u,0)\) and \((-u,0)\) have equal readings.
* id, E, E∘L: fix \(u=1/4\) and compare the two states with invariants \(r\) and \(-r\). Equality of all three occurs for some \(r\in(3/4,1)\) by the intermediate value theorem: the last squared-read difference is positive at \(r=3/4\) and negative at \(r=1\), while the first two reads agree identically.

These examples do NOT show that *every possible* triple fails.


## A stronger three-probe obstruction with two fixed coordinate reads

**Topological lemma (paper proof):** For any continuous \(f:\mathbb R^2\to\mathbb R\),
\[
(u,v)\mapsto(u^2,v^2,f(u,v))
\]
is **not injective**. Equivalently, no third continuous scalar reading can complete the two base readings \(p(u,v)\) and \(p(L(u,v))\) into an injective global signature, even if that reading is not constructed from E or L.

**Proof by intermediate value.** If \(f(a,0)=f(-a,0)\) for some \(a>0\), or \(f(0,b)=f(0,-b)\) for some \(b>0\), the corresponding pair immediately gives a collision. Otherwise choose any \(a,b>0\). Set
\[
\Delta_x=f(a,0)-f(-a,0)\ne0,\qquad
\Delta_y=f(0,b)-f(0,-b)\ne0.
\]
If \(\Delta_x,\Delta_y\) have opposite signs, compare
\[
g(t)=f(at,b(1-t))-f(-at,-b(1-t)).
\]
Its endpoint values are \(g(0)=\Delta_y\) and \(g(1)=\Delta_x\), so some \(t\in(0,1)\) satisfies \(g(t)=0\). The two states are negatives of each other and have the same coordinate squares.

If \(\Delta_x,\Delta_y\) have the same sign, compare instead
\[
h(t)=f(at,-b(1-t))-f(-at,b(1-t)).
\]
Now \(h(0)=-\Delta_y\) and \(h(1)=\Delta_x\), so again the intermediate value theorem produces a collision for the same pair of coordinate-square readings. QED.

This result proves **four is the minimum among protocols that keep both identity and L readings**. It does **not** rule out an alternative three-word signature that uses none or only one of these two fixed coordinate reads.

## Verification

* Exact rational regression checks over the 49-point integer grid, 169-point half-integer grid, and 841-point half-integer grid.
* Factor identities checked with exact rational arithmetic at a range of nonzero values.
* Intermediate-value signs for the third triple checked with exact Fractions.
* No Lean result should be claimed for this new four-probe statement until a successful exact-head CI on a proof module.

## Limits

The probability measure uses a specific coordinate frame and the already-known invariant \(I\). This is a model-specific observability theorem, not general recovery of arbitrary manifolds or stable global inversion. The origin flatness and nonuniform conditioning results from #237 remain true.
