# Exact minimax separation for two interior PAD probes
Research note, 2026-11-08 JST.

## Conditions
Toy model F_P(s)=p0+p1*s+p2*s^2+p3*s^3. The two unknown profiles each have mass 1 and mean 3/2, with nonnegative coefficients. Calibration hypotheses are FIXED to alpha_P=1 and alpha_Q=4/3. This is a hypothesis-comparison statement, not a theorem about unknown alpha, real experimental PAD calibration, physical electron transport, or measured noise covariance.

## Uniform exact inequality
Write G(t)=F_P(t^3)-F_Q(t^4). For t3=1/2 (u3=1/8) and t4=9/10 (u4=729/1000), put

L=1812744140625/2126873677106,
M=314129536481/2126873677106,
delta=2823749272953/68059957667392.

L,M>0, L+M=1, and for EVERY mass/mean-matched P,Q, the following exact dual identity holds:

L G(9/10) - M G(1/2)
 = delta
 + (859005471493/34029978833696)*p1
 + (1702471931945/272239830669568)*p3
 + (987235535475/34029978833696)*q2.

All surplus coefficients are strictly positive. Therefore for nonnegative distributions,

 max(abs(G(1/2)),abs(G(9/10))) >= delta ~= 0.04148914236404.

The exact inequality is stronger than separation of the particular tripleP/tripleQ witness in PR #103: it applies uniformly to ALL nonnegative profiles of the given common mass and mean for these FIXED alpha hypotheses and probe coordinates.

## Sharpness and positivity
The bound is attained for the CLOSED nonnegative simplex at
 P=(1/4,0,3/4,0),
 Q=(-1/2+2d,3/2-3d,0,d),
 d=416199750000/1063436838553.
These profiles have nonnegative components, mass 1 and mean 3/2, and satisfy G(1/2)=-delta, G(9/10)=delta exactly.

The infimum over strictly positive profiles is also delta, by mixing each profile with the strictly positive uniform (1/4,1/4,1/4,1/4), which also has mass 1 and mean 3/2. For mixing weight eps>0, every component becomes positive while the response gaps approach the boundary witness as eps tends to zero.

At original fourth u=64/125 the similarly computed exact minimax gap is 6098984073/392987202572 ~= 0.0155195488. With fourth u=729/1000, the worst-case separation is therefore approximately 2.67 times as large. A numerical scan places a possible design maximum near cube root t=0.92785 (u approximately 0.7988), but NO theorem of universal optimality across u has been asserted.

## Noise interpretation
If the two hypotheses each have coordinatewise observation error bounded by eps and their noiseless predictions differ by at least delta in infinity norm, the observed epsilon-neighborhoods of the hypothesis sets cannot intersect when 2*eps<delta. This is a DETERMINISTIC bound for FIXED alpha hypotheses and known mass/mean, NOT an estimate of noise standard deviation or experimental signal-to-noise ratio.

## Proof boundaries
The Lean sidecar PADFourLayerUniformMargin.lean proves the rational dual identity, positivity of coefficients, nonnegative endpoint witness, and exact signed margin dichotomy for parameterized profiles. The parameterization
P(a,b)=(-1/2+a+2b,3/2-2a-3b,a,b)
is exactly the mass=1, mean=3/2 constraint. The independent Fraction checker verifies its affine dual identity on a basis (which suffices for all rational parameters) and sharpness at the boundary. Existing PR #101/#103/#106/#109 sources are unchanged.
