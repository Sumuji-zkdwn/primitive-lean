# Siphon as an interaction-body minimal test (2026-11-08)

## Purpose and scope

Use an ordinary siphon to distinguish (i) path invariants induced by a state
observable from (ii) physical responses dependent on the tube and the medium.
This is a *minimal example*, not a new fluid theory or a derivation of the
Navier–Stokes equations. Existing Elastica notation is used: E is a chosen
scalar readout. The finite formalization uses integer-valued E for arithmetic
simplicity; physical head is a different, real-valued specialization.

## Exact algebraic statement

For an ordered path a = x_0, ..., x_n, put

    delta_E(x_i, x_{i+1}) = E(x_{i+1}) - E(x_i).

Then, with the empty path convention:

    sum_i delta_E(x_i, x_{i+1}) = E(x_n) - E(x_0).

All replacements of the interior of the operation word that retain its
endpoints preserve this quantity. This is just telescoping, not a physical
conservation law. This exactness property also gives a useful converse:
for a *complete* directed pair law w on a nonempty state set,

    (for all a,b,c, w(a,b) + w(b,c) = w(a,c))
      iff
    (there exists E with w(a,b) = E(b)-E(a)).

The potential can be reconstructed from an arbitrary anchor o as E(x)=w(o,x).
The additive constant is unobservable. This is the candidate foundational
invariant: the obstruction to representing local changes by one global E.
It overlaps with classical coboundaries / exact 1-cochains; no novelty claimed.

Counterexample: w(0,1)=1 and w(a,b)=0 for all other ordered pairs on
{0,1,2}. Then w(0,1)+w(1,2)=1 while w(0,2)=0, so no global E exists.

Two paths that begin at height 1 and end at 0, [1,4,0] and [1,4,2,0],
have equal cumulative height change -1. But their segment counts (2,3) differ,
so a non-exact cost of 1 per segment distinguishes them. Segment count is a
toy for path-dependent costs, not a calibrated model of hydraulic resistance.

## What the siphon does (and does not) establish

In a standard reservoir-to-atmosphere siphon, with z_A the initial free
surface elevation and z_B the discharge elevation, the vertical difference
z_A-z_B supplies a driving head. Raising the tube apex does **not** create
additional driving head. At steady state, the total mechanical head

    H = z + p/(rho*g) + v^2/(2*g)

is constant along a lossless streamline; in a real tube it decreases along
the flow by irreversible losses. For the simple illustrative constant-section,
constant-f model with negligible minor losses, the exit speed satisfies

    v = sqrt(2*g*(z_A-z_B)/(1+f*L/D)).

For z_A-z_B=2 m, f=0.03, D=0.02 m, L=8 m versus 12 m:

    v_8 = sqrt(39.24/13) = 1.7373 m/s;
    v_12 = sqrt(39.24/19) = 1.4371 m/s.

These are illustrative predicted values, not measured flow or a fluid solver.
At a fixed speed, lossless Bernoulli gives the apex-pressure estimate

    p_C = p_atm + rho*g*(z_A-z_C) - rho*v^2/2.

Thus moving z_C from 3 m to 5 m with z_A=2 m lowers the estimated apex
pressure by 19.62 kPa even when the endpoint height difference is unchanged.
If vapor/gas nucleation breaks the water column, the simple model no longer
applies. A 15 m siphon with degassed water was demonstrated in 2015; this does
not license ignoring tension, nucleation and cavitation constraints.

Literature: Boatwright, Hughes & Barry, *The height limit of a siphon*,
Scientific Reports 5:16790 (2015), DOI 10.1038/srep16790,
https://www.nature.com/articles/srep16790

## Verification and remaining unknowns

- Formal source: `lean/Research/SiphonInteraction.lean`, four named theorems,
  with axiom inspections. Local environment does not have Lean: the Lean
  kernel outcome must be read from the GitHub Actions run for this PR.
- Independent finite check: `python -m unittest discover -s tests
  -p 'test_siphon_interaction.py' -v` — five checks, including 29,484
  finite paths and all 19,683 directed 3-state edge labellings with values
  in {-1,0,1}. There are 7 potential-derived cases in this finite grid.
- Not proved: pressure or flow from the pure abstract E; full fluid dynamics;
  a new universal invariant; physical validity outside the stated model;
  an actual water experiment.

**Next minimal experiment:** hold reservoir/outlet elevations constant while
changing one tube length or crest elevation. Measure flow and crest pressure;
compare the unchanged endpoint state difference with the changed physical
response. Stop if the tube loses prime, and record it as a model boundary.
