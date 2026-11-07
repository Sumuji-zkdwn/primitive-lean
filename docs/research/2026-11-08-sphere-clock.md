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
