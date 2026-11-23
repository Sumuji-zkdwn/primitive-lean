# North Hopf local homeomorphism: explicit fibre chart

Date: 2026-11-23 JST.
Stacked on draft PR #229 (verified Lean algebraic north chart).

## Statement

For B_N={b in S2 | 1+b_z>0} and E_N=Hopf^{-1}(B_N) in S3, construct a Mathlib Homeomorph

    E_N ≃ₜ B_N × U(1).

The forward map is (base projection, real dot/skew reconstructed phase)
and the inverse rotates the north section by that phase.

The algebraic inverse laws were already verified as
KKHopfNorthTriv.northTrivialization in dedicated CI 45120187302.

This extension proves the functions defining the north section are
continuous on B_N; the square-root denominator sqrt(2(1+b_z)) is nonzero.
It then proves that the base, phase, and rotation maps are continuous
coordinate by coordinate, using the same inverse maps as the earlier Equiv.

## Limits

This is a topological local trivialization of the north patch, not a
smooth diffeomorphism and not yet a full two-chart principal U(1)
bundle. The south patch, smooth transitions, Chern-degree and universal
GH/EMD curvature theorems in Lean remain separate objectives.

The module is a proof candidate until exact-head trust-zero CI passes.
Do not merge automatically.
