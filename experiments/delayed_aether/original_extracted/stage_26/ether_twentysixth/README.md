# Ether v26 — covariant curvature-memory canonical repair

研究記録: `RESEARCH_NOTE_2026-11-23_v26.md`

- `verify_v26.py` — exact SymPy momenta/Legendre/canonical brackets; JAX Bianchi I Hamiltonian IVP; RK4 vs DOP853; plots and CSV.
- `independent_audit_v26.py` — NumPy direct numerical Lagrangian/Legendre/finite-difference derivatives, independent trajectory reconstruction.
- `audit_v26.json`, `independent_audit_v26.json` — assertions and numerical precision.
- `bianchi_evolution_v26.csv`, `naive_comparison_v26.csv`, `integration_convergence_v26.csv` — raw numeric history and convergence.
- `coupled_dynamics_v26.png`, `constraint_comparison_v26.png`, `integrator_refinement_v26.png` — experiment plots.

Run:
```
python verify_v26.py
python independent_audit_v26.py
```

Requires Python packages `numpy sympy scipy jax matplotlib`.

IMPORTANT: This uses the known nonminimally coupled scalar-tensor gravity action as input. It does NOT derive general relativity or gravity from a primitive elastic medium. The Bianchi I test is homogeneous (zero spatial curvature) and does not establish inhomogeneous Dirac-algebra closure, irreversible memory, topological particle stability, or gravitational-wave predictions.
