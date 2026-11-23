# 4D Regge 1-5 Move: Hessian and Memory Placement — v30

**Scope:** The flat Euclidean 4D Regge action on five 4-simplices formed by inserting one interior vertex into a single regular boundary 4-simplex. Boundary edges are fixed. This is a finite test of gravitational gauge-like vertex displacement zero modes **after** the Einstein-Regge action is assumed, NOT emergent gravity and NOT a graviton propagation calculation.

## Commands

```sh
python verify_v30.py
python independent_audit_v30.py
```

Requirements: Python 3.10+, numpy, sympy, mpmath, matplotlib (all open-source). No network access required.

`verify_v30.py` reconstructs dihedral angles for all five 4-simplices from edge lengths, computes bulk deficits and boundary exterior angles, and independently compares the full action's finite differences to its Schlaefli-reduced gradient. It analytically certifies H = 8 sqrt(5) * all-ones at the regular centered point, and verifies four gauge null directions at both centered and displaced interior vertices. The result matches standard linearized Regge theory.

`independent_audit_v30.py` independently computes the COMPLETE symmetric-family action and its first and second derivatives at 80-digit precision using mpmath, with an independently simplified boundary-angle formula.

The curvature-memory comparison holds ONLY for the static quadratic expansion at memory equilibrium. Dynamics, causality, constraints for nonlinear curved geometries, and emergence of the Einstein-Hilbert action are NOT demonstrated.

## Data files

- `RESEARCH_NOTE_2026-11-23_v30.md`: Japanese research note with derivation, tables, scope, limitations and references.
- `audit_v30.json`: finite numerical audit, flat vertex motion, curvature and memory Hessians.
- `independent_audit_v30.json`: high-precision independent action differentiation.
- `symbolic_certificate_v30.json`: exact symbolic Hessian entry.
- `mode_comparison_v30.csv`: Regge vs spring stiffness for vertex displacement modes.
- `flat_vs_curved_v30.csv`: scans of the complete Regge action and spring comparison.
- `regge_vs_elasticity_v30.png`: figure.
- `SHA256SUMS.txt`: integrity manifest (excluding self and ZIP).

No Lean proof or repository update has been performed.
