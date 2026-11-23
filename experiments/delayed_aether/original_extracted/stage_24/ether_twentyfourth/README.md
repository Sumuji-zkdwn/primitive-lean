# V24 — Matter-sector hypersurface bracket and delayed-hardening compatibility

The previous stage V23 verified time-dependent spatial-coordinate covariance in an ADM reduction with two transverse polarizations and reversible memory fields. V24 calculates the **matter** Hamiltonian-Hamiltonian Poisson bracket for coupled scalar fields on a specified one-dimensional spatial metric and tests the relation needed for the standard hypersurface-deformation algebra.

Run with Python 3.10+, NumPy, SymPy, Matplotlib:

```bash
python verify_v24.py
python independent_audit_v24.py
```

Files:
- `RESEARCH_NOTE_2026-11-23_v24.md` — mathematical derivation, exact assumptions, results, limits.
- `verify_v24.py` — symbolic 2x2 matrix solution, direct discrete canonical bracket, potential cancellation, independent continuous reference, resolution scan, figures.
- `independent_audit_v24.py` — independent exact-rational 5-site SymPy bracket; a different hardening function.
- `audit_v24.json`, `exact_rational_audit_v24.json` — machine-readable audit.
- `bracket_convergence_v24.csv`, `gradient_audit_v24.csv` — numerical evidence.
- `constraint_closure_v24.png` — convergence to the standard momentum generator vs non-closure of mismatched stiffness.
- `bracket_discretization_v24.png` — convergence toward each model's own continuum prediction.
- `characteristic_speeds_v24.png` — matched and mismatched local front speeds.

**Scope warning:** These are not full Hamiltonian + diffeomorphism constraints of dynamical 3+1 general relativity; gravity is not derived, the metric is externally supplied, and the memory field is reversible. No independent physical prediction is claimed. Finite-lattice closure is not exact; the correct matched model converges as resolution improves.
