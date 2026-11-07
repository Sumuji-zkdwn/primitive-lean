# Two-amplitude appearance: an obstruction and its exact repair

Date: 2026-11-06. Base main: `67fdf6b74bbbcb20dc70e7bf98b90471e329aa91`. PR #86.

## Defined model, not a particle claim

Let B,D be complex amplitudes and observe Q=B conjugate(D). Choose the update
B'=cB-isD, D'=cD-isB, with real c,s. For c^2+s^2=1 this preserves
N=|B|^2+|D|^2. The names dark/bright are working labels, not distinct measured
particle species. The observation retains Re Q AND Im Q, not just |Q|^2.
The update is supplied; it is not derived from an energy, field equation or
space-time dynamics. In particular, Q is not established as a photon amplitude.

Put R=Re Q, I=Im Q and Z=|B|^2-|D|^2. Exact expansion gives

R'=(c^2+s^2)R,
I'=(c^2-s^2)I+csZ,
Z'=(c^2-s^2)Z-4csI.

## Main theorem and witness

`output_closes_iff`: there is a function f satisfying Q'=f(Q) for ALL
internal amplitude pairs if and only if cs=0. Necessity already follows
from (B,D)=(1,0),(0,1): both have Q=0,N=1 but next coherences are +/-ics.
For sufficiency drop the csZ term. At unit norm the two exceptional cases
are no mixing and complete exchange, not arbitrary weak coupling.

For a witness with both components nonzero, choose c=3/5,s=4/5.
(B,D)=(1,2) and (2,1) both give Q=2,N=5, but one pulse yields
Q'=2-36i/25 and Q'=2+36i/25. Thus knowing even Q AND N does not suffice.

The repair is not to retain the entire internal state. Retain (R,I,Z).
It obeys the above closed evolution, and

Z=(25 Im Q_next+7 Im Q_now)/12.

## Actual native-source bridge

The workflow concatenates the unchanged, actual
`linear_input/lean_check/OperatorWordObservations.inc` with
`lean/DarkBrightObservationBridgeTail.inc`, importing the new standalone
`lean/DarkBrightObservation.lean`. It uses the original WordEq and
representation_word_eq, rather than duplicating their definitions.

For the fixed 3/5,4/5 pulse and arbitrary real amplitude coordinates:

WordEq output step x y iff summary x=summary y
                         iff current AND next readouts agree.

The forward direction recovers Z from the two readouts. The reverse direction
uses the exact descended evolution and the original representation theorem.
`native_predictive_minimal` proves kernel minimality: any exact predictive
representation can identify only pairs with the same summary. This is NOT
a claim that no set-theoretic encoding into fewer real coordinates exists.

## Geometry and invisible freedom

`sphere_identity`: 4|Q|^2+Z^2=N^2. At fixed N the scaled summary
(2R,2I,Z) lies on a sphere. `delta_sign_ambiguity`: fixed Q and N determine
Z only up to sign. A common unit complex phase leaves the summary unchanged,
and `native_common_phase_invisible` extends this to every permitted word.
The formal file proves this invisibility direction, not a separate theorem
that every equal-summary pair is a common-phase orbit.

Up to ordering and sign convention these quantities are the usual pure-state
Stokes coordinates when B,D are interpreted as two polarization amplitudes.
This comparison identifies an existing mathematical structure, not evidence
that vacuum photons are composite particles. See the explicit formulas in
Ansys Optics, 'Calculation of Stokes Parameters':
https://optics.ansys.com/hc/en-us/articles/30220581229459-Calculation-of-Stokes-Parameters

## Intensity-only observer boundary

For the observer |Q|^2, swapping B,D leaves the readout unchanged and commutes
with every chosen mixer. Consequently the displayed swapped pair cannot be
distinguished by any number of these pulses if only |Q|^2 is measured.
This statement is proved in the independent add-on module
`lean/DarkBrightIntensity.lean`; it is separate from the original 28 theorems
in this PR. Optical total intensity N is a different quantity from this toy
product intensity |Q|^2. Verification details are in
`docs/verification/2026-11-07-dark-bright-intensity-symmetry.md`.

## Finite regression and verification record

`python tools/check_dark_bright_observation.py` uses Fraction arithmetic on
625 states with coordinates in {-2,-1,0,1,2}. Local checks pass:
625 sphere identities; 625 reconstructions; 4375 mixer/norm checks;
3125 phase checks; 8125 trace/swap-intensity checks; 7 closure witnesses.
On this sample, current coherence has 73 classes; summary, two-readout and
12-step-trace partitions all have exactly 151 classes. These finite counts
are not cardinalities of the infinite state space and are not Lean proofs.

The new Lean sources contain 28 candidate theorem declarations, including
five original-source bridge theorems. Exact-head verification is required:
pinned Lean 4.30.0-rc2 and pinned Mathlib, `--trust=0`, and a complete added-
theorem axiom audit. The first run 42204496683 at 7797cba failed on two proof
elaboration details; this revision repairs them without changing statements.
The final successful source SHA/run, if obtained, is recorded in the PR.
Do not treat this note's candidate count as successful verification by itself.

The isolated workflow does not register this module in the old all-library
registry. No canonical proof source, integration manifest or pinned dependency
is modified. No quantization, photon counting, helicity, propagation speed,
Maxwell equation or experimental validation is established here.
