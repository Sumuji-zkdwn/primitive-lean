# Ether v17: Einstein–Skyrme–chi dynamically coupled spherical test

This is a **test implementation**, not a derivation of gravity from an ether.

The new feature over v16 is time-dependent polar-areal metric reconstruction **at every matter step**, with an *independent* Einstein momentum equation audit and a frozen-metric comparison.

Dependencies: Python 3.11+, `numpy`, `scipy`, `matplotlib`. No external data required.

Run in this order:

```bash
python verify_v17.py     # short histories, table, and sample metric profiles
python audit_v17.py      # independent Hamilton variation, radial ODE, frozen-metric check
python figures_v17.py    # longer run, convergence, figures
```

Output files include `summary.json`, `extended_summary.json`, `independent_audit.json`, CSVs and PNG figures. Source formulas, units, boundary conditions and limitations in `RESEARCH_NOTE_2026-11-22_v17.md`.

The executable evolves a hedgehog **only**: its boundary degree `B=1` is assumed, not nonradial topological stability. A separate reversible scalar `chi` creates response lag but no entropy-producing dissipation. Strong-field causality and Lorentz symmetry beyond the selected covariant action are not proven.
