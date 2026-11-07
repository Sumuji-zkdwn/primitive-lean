# Gravitational F0 observational quotient (2026-11-03)

Source: `GravityObserver.inc` on top of `GravityCocycle.inc` (PR #41)
and the existing `LinearInputF0.Idempotent`.

## Model
Two equal unit masses at `-a,+a` are observed from `R>|a|` on a line.
A normalized potential probe is
`P(R,a)=1/(R-a)+1/(R+a)=2R/(R²-a²)`.

1. The mass-only map `a ↦ 0` is idempotent (F0), but a decoder of its
   output cannot reproduce this potential for every `0≤a<R`.
2. The reflection quotient `a ↦ |a|` is idempotent and leaves the
   normalized potential exactly unchanged.
3. For `|a|,|b|<R`, equality `P(R,a)=P(R,b)` holds precisely when
   `|a|=|b|`. A single external probe identifies **unsigned** separation
   within this restricted symmetric family, not its signed orientation.
4. The quadratic correction and an exact next nonzero term are
   `P(R,a)-2/R=2a²/[R(R²-a²)]` and
   `P(R,a)=2/R+2a²/R³+2a⁴/[R³(R²-a²)]`.

## Evidence and limitations
This is an additional proposed finite-dimensional theorem set, not
universal gravitational tomography. The observer position is fixed, the
two sources have equal masses and symmetric locations, and the `1/r`
potential has been chosen, not proved from the chain's cocycle law.
No arbitrary 3D uniqueness, no general convergence of a multipole series,
no self-collision treatment, no inverse-square characterization, and no
Einstein equations are claimed.

The independent Lean probe compiles the cocycle and new theorems with
a locally stated replica of the original F0 `Idempotent` predicate
only to make a fast diagnostic. Formal connection to the **actual**
F0 definition must be certified by the full joint Lean audit in
`tools/verify.py --integration-only`.

Until matching CI logs show success for the exact commit,
all new lemmas remain proof candidates.
