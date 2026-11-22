# Ether field-to-geometry research: V5

An explicitly limited toy-model study of a Lorentz-invariant two-field kinetic coupling, static impedance scattering, Derrick's static-soliton obstruction, a classical BPS monopole benchmark, and conformal scalar-gravity lensing failure.

This work **does not derive general relativity, electromagnetism, quantum mechanics, actual ether, or the Standard Model**. A fixed Minkowski spacetime is assumed by the two-field theory. The BPS benchmark uses an **additional** non-Abelian gauge field, not derived from the two fields. The nonlinear memory is conservative, not dissipative. The frozen interface scattering test is not a self-consistent dynamic solution.

Files:
- `RESEARCH_NOTE_2026-11-22_v5.md`: Japanese technical note with detailed assumptions, proofs, interpretation, and links.
- `verify_v5.py`: the action-consistent 1D time evolution, cone-factorization numerical checks, interface scattering, energy scaling, and lensing calculations.
- `monopole_benchmark.py`: independent published BPS solution reproduction.
- `weak_field_lensing.py`: check the required non-conformal weak-field spatial metric parameter gamma.
- `audit_independent.py`: reopens generated data files and tests results.
- `audit_results.json`, `audit.txt`, `monopole_benchmark.json`: machine readable checks.
- `*.csv`, `*.png`: output data and charts.

Run:

```bash
python -m pip install numpy scipy matplotlib
OPENBLAS_NUM_THREADS=1 python verify_v5.py
OPENBLAS_NUM_THREADS=1 python monopole_benchmark.py
OPENBLAS_NUM_THREADS=1 python weak_field_lensing.py
OPENBLAS_NUM_THREADS=1 python audit_independent.py
```

Python 3.11+ recommended. Runtime is CPU moderate (256 and 512 grid DOP853). No training data or external internet calls are required.
