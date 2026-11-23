# Finite probabilistic tangent observability for the siphon E map

Date: 2026-11-23. This is an independent *paper proof* and an exact-arithmetic finite check; the new theorem has **not** yet been verified by the Lean kernel.

## Existing maps and a coordinate-minor probability

Take the existing maps from Research.SiphonPolynomialE and OrbitTrace:

\[
 r=I(u,v)=v+u^3,\quad E(u,v)=(u+r^2,\;r-(u+r^2)^3),\quad L(u,v)=(v,v-u).
\]

A tangent vector to the level curve \(I(u,v)=r\) is \(t=(1,-3u^2)\). The normalized squared coordinate minors give a two-point probability

\[
 P(u,v)=(p_1(u),p_2(u))=
 \left(\frac1{1+9u^4},\frac{9u^4}{1+9u^4}\right).
\]

Importantly, this probability is coordinate-dependent. A single reading loses the sign of \(u\), and says nothing directly about \(v\).

Consider the five-word observation

\[
 \Phi(z)=\big(P(z),P(Ez),P(E^2z),P(Lz),P(E(Lz))\big).
\]

**Theorem (paper proof):** The map \(\Phi:\mathbb R^2\to(\Delta^1)^5\) is injective. Only the first component of each two-point probability is required.

## Algebraic proof

Because \(p_1(u)=1/(1+9u^4)\), equality of the probabilities from two first-coordinate values \(x,y\) is equivalent to \(x^4=y^4\), and hence to \(x^2=y^2\) over the real numbers.

Put \(a=r^2\ge0\). The first coordinate after \(n\) iterations of E is \(u+na\). Thus the first three probability readings determine

\[
 b_0=u^2,\qquad b_1=(u+a)^2,\qquad b_2=(u+2a)^2.
\]

Their second difference equals \(b_2-2b_1+b_0=2a^2\), fixing \(a\) uniquely because \(a\ge0\).

If \(a>0\), then
\[
 u=\frac{b_1-b_0-a^2}{2a}
\]
is uniquely determined. The only remaining ambiguity is \(r=+\sqrt a\) versus \(r=-\sqrt a\), with \(v=r-u^3\).

If \(u\ne0\), the L reading distinguishes these possibilities because the squared first-coordinate values differ by
\[
 (r-u^3)^2-(-r-u^3)^2=-4ru^3\ne0.
\]
If \(u=0\), the L reading alone cannot distinguish the signs, but the first coordinate after E composed with L is \(r+(r+r^3)^2\). Its squared values for opposite signs differ by
\[
 [r+(r+r^3)^2]^2-[-r+(-r+(-r)^3)^2]^2
 =4r^3(1+r^2)^2\ne0.
\]

If \(a=0\), then \(r=0\), \(v=-u^3\), and the first three readings determine only \(u=\pm\sqrt{b_0}\). At \(u=0\) these agree. Otherwise set
\(C=u^2(1+u^2+u^8)^2>0\).
For the opposite candidate signs, the first coordinate after E composed with L is \(C-u^3\) versus \(C+u^3\). Their squared values differ by
\[
 (C-u^3)^2-(C+u^3)^2
 =-4u^5(1+u^2+u^8)^2\ne0.
\]

Thus the last two readings remove every remaining sign ambiguity and \(\Phi\) is injective. The argument uses exact polynomial identities and works for **every real state**, not just enumerated states.

## Constructive reconstruction

Each scalar probability reading \(p\) determines the nonnegative squared first coordinate \(b=\sqrt{(1/p-1)/9}\).
Use the first three \(b_i\) to obtain \(a=\sqrt{(b_2-2b_1+b_0)/2}\). If \(a>0\), recover \(u\) from the formula above and test \(r=\pm\sqrt a\) against the L and E-after-L readings. If \(a=0\), test \(u=\pm\sqrt{b_0}\) with \(r=0\). In either case recover \(v=r-u^3\).

The exact Python unit test is at tests/test_siphon_e_distribution_observability.py. It has no non-standard dependencies, uses fractions.Fraction and math.isqrt, and has five tests, including full reconstruction of every state in each finite grid:

| State grid | after identity | plus E | plus E² | plus L | plus E after L |
| --- | ---: | ---: | ---: | ---: | ---: |
| 49 integer points | 4 | 41 | 41 | 45 | **49** |
| 169 half-integer points | 7 | 152 | 154 | 162 | **169** |

Run: python3 -m unittest discover -s tests -p 'test_siphon_e_distribution_observability.py' -v

## Scope and caveats

- The real-algebraic argument establishes five-reading *state identification* for the specified E, L and the given P.
- The finite Python tests confirm the constructive inverse on two grids; they are not a Lean proof or evidence about arbitrary untested noisy distributions.
- Existing Lean results establish invertibility of E, preservation of I, its determinant-one identity, and earlier *position* observation theorems. They do **not** automatically certify the new probability-only observation theorem.
- The model presupposes the invariant I and a coordinate system. P depends on those choices; the result is not a proof of the general machine-learning manifold hypothesis or of coordinate-invariant reconstruction of an unknown manifold.
- No claim is made that these five probes are minimal, or stable under noise. Both questions remain open for this construction.

Useful next tests: coordinate-free alternatives to P, quantitative noise stability, and a Lean kernel theorem corresponding to the five-reading algebraic proof.
