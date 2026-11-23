# Delayed geometry & local topological degree — verification v11

This is a finite mathematical testbed, **not a derivation of gravity or a physical ether**. The box has a fixed (non-periodic) exterior value; the interior 4-component unit field can carry a degree. Its discrete texture is coupled to tetrahedral edge lengths by a *chosen constitutive equation*. The memory obeys a dissipative evolution, with prescribed driving of the topological field.

## Reproduce

Python 3.10+ (tested with Python 3.13), NumPy, SciPy, SymPy, Matplotlib.

```bash
python -m pip install numpy scipy sympy matplotlib
OPENBLAS_NUM_THREADS=1 python verify_v11.py
OPENBLAS_NUM_THREADS=1 python exact_degree_v11.py
OPENBLAS_NUM_THREADS=1 python energy_v11.py
OPENBLAS_NUM_THREADS=1 python memory_v11.py
python plot_curvature_v11.py
OPENBLAS_NUM_THREADS=1 python audit_assert_v11.py
```

`RESEARCH_NOTE_2026-11-22_v11.md` is the primary technical report. The corresponding JSON audits, CSV calculations, plots, and source code are included. `SHA256SUMS.txt` has hashes of the bundled files; hashes exclude that manifest itself.

1. `verify_v11.py` computes preimage degrees, resolution failures, tetrahedral Regge deficits and a pure-coordinate-warp negative control.
2. `exact_degree_v11.py` provides rational-arithmetic certificates (n=6, n=8) that the normalized affine interpolation never vanishes and has degree -1.
3. `energy_v11.py` tests the `E2 + k4 E4` energy against the exact scaling profile.
4. `memory_v11.py` evolves a delayed intrinsic metric with positive memory potential; local hardening feeds back into the memory force, and bookkeeping separates prescribed work and dissipation.
5. `audit_assert_v11.py` verifies invariant, negative-control, convergence and energy-balance conditions.

Every model uses dimensionless values. Do not interpret the Regge-deficit proxy as Einstein curvature, the prescribed core motion as a freely moving particle, or the topological charge as observed mass.
