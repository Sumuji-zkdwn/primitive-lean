# Ether model v19 — stationary profile and restricted l=2,3 modes

An independently runnable continuation of the v18 static Skyrme-chi model (2026-11-22).

**What is validated**: the original v18 seed is not stationary; flat-space equilibrium profiles for five radial resolutions; six independent initial radii converge to the same n120 minimum; Hessians of radial perturbations and two restricted nonradial trial families; independent gradient/second-variation verification; nine final audit assertions.

**What is not validated**: global minimizer, full 3D second variation (orientation modes omitted), non-spherical self-gravitating Einstein dynamics, irreversible memory or an emergent derivation of gravity.

## Files

- `RESEARCH_NOTE_2026-11-22_v19.md`: model, results, mathematical bound, assumptions, limitations.
- `verify_v19.py`: optimize the stationary profiles, construct restricted angular Hessians and kinetic matrices.
- `robustness_v19.py`: 6 multistarts, n240/320 continuation and alternative angular trial bases.
- `independent_audit_v19.py`: PyTorch autograd, radial Hessian symmetry, angular quadrature.
- `final_audit_v19.py`: machine-checkable, fail-closed review of generated data.
- `figures_v19.py`: plots from the result files.
- `.csv`, `.json`, `.png`: measured profiles, Hessians, spectra and plots.

## Reproduction

```bash
OPENBLAS_NUM_THREADS=1 python verify_v19.py
OPENBLAS_NUM_THREADS=1 python independent_audit_v19.py
OPENBLAS_NUM_THREADS=1 python robustness_v19.py
OPENBLAS_NUM_THREADS=1 python final_audit_v19.py
OPENBLAS_NUM_THREADS=1 python figures_v19.py
```

Dependencies: `numpy scipy matplotlib torch` (CPU). Re-running modifies files in this directory, so use a copy for independent comparison. `final_audit_v19.py` fails if any of its nine checks fail.
