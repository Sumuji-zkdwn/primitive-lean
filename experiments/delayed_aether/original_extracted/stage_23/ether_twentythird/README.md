# V23 | nonlinear spatial gauge and coupled memory in a 1+2 reduction

Read `RESEARCH_NOTE_2026-11-23_v23.md` for derivations, scope and limitations.

Run from any working directory:

```
python verify_v23.py
python independent_audit_v23.py
python cross_polarized_wave_v23.py
```

Requirements: Python 3.10+, numpy, sympy, matplotlib. No network required.

The scripts provide three independent checks:

1. Off-shell covariance of a spatially varying ADM action under time-dependent x relabelings with nonzero shift and nonlinear transverse metric. Also two deliberately wrong transformations and a curvature-squared counterexample.
2. SymPy 4D Christoffel/Ricci computation from a general two-by-two transverse metric, and exact algebra for a cross-polarized plane wave.
3. A 601-point numerical 4D curvature / ADM Hamiltonian / momentum constraint audit of a nonlinear crossed-polarization Einstein-two-scalar solution.

**Caution**: Einstein-Hilbert/ADM dynamics is *assumed*, not derived from medium mechanics. The exact plane wave has q=z so no memory lag/hardening. No experimental prediction or new gravity theory is claimed.
