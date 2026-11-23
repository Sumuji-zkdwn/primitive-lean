# Ether model V4 — reproducible finite computations

English summary: A mathematical toy model based on the Skyrme static energy, a massless scalar and viscoelastic strain memory. This is **not** an experimentally validated theory of gravity, light or matter. See `RESEARCH_NOTE_2026-11-22_v4.md` for assumptions, proofs, counterexamples and numeric scope (Japanese).

Python 3 with `numpy`, `scipy`, `matplotlib` is required. All the `.py` files and data are in this directory. Static radial solver from V3 is duplicated locally for self-contained reruns.

```bash
OPENBLAS_NUM_THREADS=1 python analytic_bounds.py
OPENBLAS_NUM_THREADS=1 python dispersion_audit.py
OPENBLAS_NUM_THREADS=1 python strain_cone_no_go.py
OPENBLAS_NUM_THREADS=1 python mass_charge_audit.py
OPENBLAS_NUM_THREADS=1 python nonradial_3d.py
OPENBLAS_NUM_THREADS=1 python nonradial_3d.py --fine
OPENBLAS_NUM_THREADS=1 python saturated_memory_dynamics.py
OPENBLAS_NUM_THREADS=1 python audit_v4.py
```

`nonradial_3d.py` default runs 49³,61³; `--fine` runs 91³; `--fast` runs a 41³ smoke test. Full rerun is not instantaneous; memory scales as O(n³). `audit_v4.py` depends on all generated data files. All numerical stability results are limited to selected perturbation directions and finite times. Background signal speeds and stress-energy universal coupling remain **unresolved**.

Some CSVs and plots use the exact central-difference factor `2*dx` (a preliminary erroneous factor was found and corrected before the final V4 audit). The scripts are included to permit independent inspection.
