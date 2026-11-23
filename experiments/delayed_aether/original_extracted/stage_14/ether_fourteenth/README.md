# Exponential-metric topology toy model v14

Finite 3D self-coupled q/B/Z toy model with positive-definite exponential spatial metric, topology-admissible step guard, and a separate ADM Lorentzian signature construction. NOT a derivation of general relativity. The previous-model sources (`verify_v13.py` and `verify_v11.py`) are included for reproducibility and reuse.

Requirements: Python 3.10+, numpy, scipy, matplotlib.

```
python verify_v14.py
python audit_v14.py
python plot_v14.py
```

Audit and data: `audit_v14.json`, `independent_audit_v14.json`, three `exp_n*.csv` time series, four `.png` plots, the detailed Japanese `RESEARCH_NOTE_2026-11-22_v14.md`.

Primary findings: SPD of g=exp B is automatic but does not ensure valid shared-edge tetrahedra; a finite counterexample and a conservative small-B sufficient condition are supplied. An adaptive integrator can preserve q's affine-interpolation degree over the accepted finite time interval, but can stall and does not imply an all-time unconstrained dynamics. N=e^phi>0, shift beta, and g=exp B yield Lorentzian ADM signature by construction but not Einstein's equations.
