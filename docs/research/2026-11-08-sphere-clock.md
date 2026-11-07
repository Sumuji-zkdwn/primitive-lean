# Sphere clock v0.1: scope and exact formal claims

2026-11-08 (JST). Based on the existing Elastica.Geometry circular arc theorems.

## Constructed model
- The original Elastica meridian, whose x and z coordinates are sin(s) and 1-cos(s), is rotated into the unit sphere (X,Y,Z)=(sin(s)cos(a),sin(s)sin(a),-cos(s)).
- The Lean theorem on_unit_sphere proves X²+Y²+Z²=1 for all real s,a. No claim of unique parametrization at poles or seam.
- A sampled needle covers an entire longitude meridian on a finite latitude × longitude coordinate grid. The evolving dial D(t,p) counts needle passages at p.
- The Lean theorem needle_eq_dial_diff proves N(t,p)=D(t+1,p)-D(t,p); full_history_determines_route proves that complete dial histories recover the ordered route.
- A two-step counterexample gives identical final dials for longitude order false,true and true,false, while the ordered routes differ.

## Scope boundaries
No continuum-time Dirac distributions or measures, rational/irrational layer gluing, non-Hausdorff quotient, proof of physical Elastica dynamics, continuous pole-quotiented sphere grid, quantum computation, or holonomy theorem. None of the original Elastica declarations are edited. The chosen needle route is independent data.

## Verification
From repository root:
python -m unittest discover -s tests -p test_sphere_clock.py -v

From lean/ with its pinned Lean/mathlib:
lake exe cache get
lake build Elastica.Geometry
lake env lean --trust=0 Research/SphereClock.lean

The scoped workflow on proposed PR heads checks both. A Python pass alone is not proof of Lean compilation.


## v0.2 — rationally glued circle, conditional rotation obstruction

New module: lean/Research/SphereClockRationalGluing.lean.

For an additive abelian angle group G and subgroup H, use two sheets G × Bool.
Define: (x,a) ~ (y,b) iff x=y and (a=b or x in H).

The proof that this is a setoid is intrinsic: it does not assert that the
quotient is Hausdorff or embeddable as a smooth surface.

1. General theorem rotate_respects_iff: a common shift d descends through the
   gluing relation exactly when d belongs to H.
2. The instance uses Angle = AddCircle (1 : ℝ), the real circle with one full
   revolution identified with zero. rationalAngles consists of rational
   angular coordinates modulo one; rational angles glue the two sheets.
3. A full revolution is exactly the identity on the quotient
   (full_turn_is_identity).
4. hidden_layer_reappears: two states identified at zero become distinct after
   shifting representatives by any non-rational angle. An irrational shift
   DOES NOT define a map on the quotient. This is not quotient dynamics.
5. flipSpace is an explicitly chosen valid sheet permutation. The toy
   loopWithSwitch applies one full revolution PLUS this extra switch.
   It fixes rational shared states and changes non-rational states.
   The switch is an extra operation, NOT a consequence of curvature,
   Elastica dynamics, or holonomy.

The independent exact Python implementation uses a+b*sqrt(2) modulo Z
with rational a,b, and exact symbolic equality. The finite sample checks
setoid laws, rotation compatibility, full-turn equality, and switching.
It does not substitute for the general Lean statement.

Verification:
python -m unittest discover -s tests -p test_sphere_clock_rational_gluing.py -v
cd lean
lake env lean --trust=0 Research/SphereClockRationalGluing.lean

Not proved here: density of rational angles, non-Hausdorff quotient topology,
continuum Dirac measures, or physical holonomy.
