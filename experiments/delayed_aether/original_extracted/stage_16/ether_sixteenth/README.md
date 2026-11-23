# Delayed-hardening ether – verification v16

This package continues v15 with a **single generally covariant Einstein–Skyrme–memory action**. It does not derive gravity from ether.

To regenerate data, PNGs and self-audit:

```bash
python verify_v16.py
python independent_audit_v16.py
```

Install Python 3.11+ and dependencies `numpy scipy sympy matplotlib`.

Main outputs:

- `RESEARCH_NOTE_2026-11-22_v16.md`: Japanese mathematical report, action, hypotheses, metrics, caveats.
- `verify_v16.py`: generic Noether symbolic check, 1D radial Hamiltonian dynamics, 3D spherical time-symmetric Einstein Hamiltonian constraint.
- `independent_audit_v16.py`: separate finite-difference and canonical derivative checks.
- `radial_dynamics.csv`, `topological_memory_dynamics.png`, `energy_conservation.png`, `radial_profiles.png`.
- `einstein_constraint_profile.csv`, `einstein_initial_constraint.png`.
- `audit_v16.json`, `independent_audit_v16.json`: numeric findings.
- `SHA256SUMS.txt`: checksums for files in this directory excluding the checksum file itself.

Assumptions and boundaries:

- Flat-spacetime dynamics are evolved independently of curved-spacetime Einstein initial data.
- Topological degree in the dynamics is fixed by the radial hedgehog boundary, not verified for general nonspherical perturbations.
- The memory field is reversible; no dissipation in this closed action.
- The Einstein–Hilbert term and Skyrme stabilization are adopted from established physics, not derived.
- Asymptotically flat `psi=1+C/r` exterior is matched to a compactly supported matter profile at `r=12`.
