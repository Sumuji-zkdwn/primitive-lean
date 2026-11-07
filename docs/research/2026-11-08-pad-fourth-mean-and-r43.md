# PAD four interior probes, mean constraint, and the ratio 4/3
Research note: 2026-11-08 JST.

This is an additive follow-up stacked on PR #106, PR #103 and PR #101. None of their existing proofs are altered. Power-law calibration s=u^alpha is illustrative, NOT validated experimental PAD calibration.

## Exact four-probe ambiguity when mean is not shared

Let alpha_A=1, alpha_B=4/3, and use nominal u=(1/64,1/27,1/8,64/125). The additive Lean source defines two strictly positive rational profiles:

P=(155406813431861/3135446314560000, 307250787839/10451487715200, 5341857272874251/15677231572800000, 379061002125331/653217982200000)

Q=(9757217468803/196456536000000, 21675828291197/196456536000000, 4/5, 1/25).

Both masses equal 1. At all four t=(1/4,1/3,1/2,4/5), exactly F_P(t^3)=F_Q(t^4). But the means differ: mean_P approximately 2.451771073358322 and mean_Q approximately 1.8303339635958815. The Lean module checks all of these assertions by exact rational arithmetic.

Thus equality of mass ALONE is insufficient to ensure global identification by four interior probes. This is a genuine fourth-interior collision, unlike the trivial fourth probe at u=1.

## General conditional theorem for calibration ratio r=4/3

EXTERNAL ANALYTIC PROOF, not currently Lean-formalized:
Let P and Q be any positive four-layer profiles with the same mass and the same mean. If alpha_B=(4/3)alpha_A with alpha_A>0, then F_P(u^alpha_A)=F_Q(u^alpha_B) at at most THREE distinct u in (0,1). Hence any four distinct internal probes exclude cross-calibration ambiguity for this specified ratio. The PR #103 triple pair shows this upper bound of three is sharp.

Proof. Put s=u^alpha_A, with 0<s<1. The residual identity from PR #101 implies

 G(s)/(1-s)^2 = (p2-q2)+(s+2)(p3-q3) + K(s),

where G(s)=F_P(s)-F_Q(s^(4/3)) and
 K(s)=sum_{j=1}^3 q_j (s^j-s^(4j/3))/(1-s)^2.

The first two terms on the right are affine in s, so the second derivative is K''.

Write s=t^3, 0<t<1. Direct differentiation yields

 K''(s) = 2 N(t) / [9 t^2 (1-t)^3 (1+t+t^2)^4],

 N(t)=q1 A(t)+q2 B(t)+q3 C(t),

 A(t)=5t^5-4t^4-4t^3+16t^2-2t-2,
 B(t)=-t^2(t^7+t^6+t^5-7t^4-7t^3+11t^2-9t-9),
 C(t)=9t^5(1+t+t^2)(t^6-3t^3+3).

All q1,q2,q3 are strictly positive. The algebraic Bernstein certificates show B,C>0 on (0,1), and A>0 for 1/2<=t<1. Every root of N must therefore satisfy A(t)<0 and 0<t<1/2.

The polynomial derivatives dA,dB,dC and the Wronskian identities satisfy

 A dB - (dA)B = -t(t-1)^2 PB(t), with PB(t)>0 for t>0;

 A dC - (dA)C = 9t^4(t-1)^2 E(t), with E(t)<0 for 0<t<1/2.

The strict sign of E on the left half is certified by a 12-term positive-basis identity. All these rational identities and sign statements are separate Lean lemmas.

At a root N(t0)=0, eliminating q1 gives

 N'(t0) = [q2(A dB - dA B)+q3(A dC - dA C)] / A(t0) > 0.

Every zero of N is thus a strictly upward crossing. A C1 real function on a connected interval cannot have two such zeros without an intervening zero that is not an upward crossing. So N has at most one root. The positive denominator shows K'' has at most one root in (0,1).

If G/(1-s)^2 vanished at four different interior points, two applications of Rolle's theorem would force K'' to vanish at least twice. Contradiction.

IMPORTANT: Lean currently verifies only the exact rational witness, polynomial identities, Bernstein positivity certificates, and Wronskian sign statements. The real-power derivative identity, crossing-count argument, and Rolle applications are in this note only. The theorem is currently an independently algebra-checked external analytic deduction, NOT a kernel-certified universal theorem.

## Regimes and open questions

- For r=4/3, any four distinct interior probes, with common mass and mean and positive profile components: global collision excluded by the analytic proof above.
- For r>=3/2, a generalized Descartes/Laguerre sign-counting argument separately excludes four interior collisions for equal-mass positive profiles. Reference: G.J.O. Jameson, Counting zeros of generalised polynomials: Descartes' rule of signs and Laguerre's extensions, Mathematical Gazette 90 (2006), pages 223-234, DOI 10.1017/S0025557200179628.
- Other ratios 1<r<3/2: not proved either unique or ambiguous.
- No actual PAD calibration, instrumental covariance, or noise level has been established.

## Checks and next step

Run python3 tools/check_pad_fourth_mean.py for standard-library exact Fraction verification, including 20-point polynomial identity checks (all degrees at most 17). CI uses isolated Lean --trust=0 compilation and axiom printing without changing PR #101, PR #103 or PR #106. Next step is an explicit real-analysis Lean bridge: show the formal derivative polynomials match real derivatives, encode the one-upward-zero lemma, and apply Rolle twice.
