# ETHER-13: topology obstruction and dynamically generated 3D shear

**Scope:** mathematical prototype; not a derivation of general relativity or particle physics.

## Files
- `verify_v13.py`: continuous nodal homotopy to vacuum, finite-tetrahedral zero witness, dynamic q+B+Z system with 3D internal metric and viscous memory.
- `verify_v11.py`: local copy of the previously verified finite mesh/Regge curvature/degree helpers.
- `plot_v13.py`: reproducible plots plus curvature-time-series comparison.
- `audit_v13.py`: independent checks of stored results (prints PASS).
- `audit_v13.json`, `extra_controls.json`, `independent_audit.json`: detailed numerical evidence.
- `RESEARCH_NOTE_2026-11-22_v13.md`: derivation, theorem, limitations (Japanese).
- `*.csv`, `*.png`: trajectories, homotopies, figures.
- `SHA256SUMS.txt`: digests of the included files, except itself.

## Reproduce
Requires Python 3.10+, NumPy, SciPy, Matplotlib:

```bash
OPENBLAS_NUM_THREADS=1 python verify_v13.py
OPENBLAS_NUM_THREADS=1 python plot_v13.py
OPENBLAS_NUM_THREADS=1 python audit_v13.py
sha256sum -c SHA256SUMS.txt
```

Additional controls `extra_controls.json` were run with the following model configurations: uncoupled q/B; q with zero initial velocity; extended t=0.20 simulation. Their original CSV outputs are included.

The finite-grid charge preservation observed in short simulations is **not** a proof of long-term topological stability. The topological obstruction theorem pertains to the full vertex-state configuration space; the witness is a chosen continuous path in that configuration space, not a solution to the equations of motion.
