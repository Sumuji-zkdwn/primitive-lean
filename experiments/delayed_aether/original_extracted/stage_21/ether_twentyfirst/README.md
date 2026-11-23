# ether model v21 — nonlinear spin-2 self-response

**Scope:** established plane Einstein gravity (Rosen plane waves) and covariant scalar toy fields, NOT emergence of gravity or a complete gel constitutive law.

## Run

```
python verify_v21.py
python independent_audit_v21.py
```

Requires: Python 3, NumPy, SymPy, SciPy, Matplotlib. Output: `audit_v21.json`, `independent_audit_v21.json`, four CSVs and three PNG figures.

Tested:
- Exact symbolic coefficient of `epsilon^2` in the plane wave Ricci tensor;
- nonlinear Rosen plane wave vacuum and equal-scalar null-source ODE;
- separate four-dimensional Christoffel/Ricci derivation;
- independent 5-point finite-difference curvature checks on saved solution;
- null-lagged interacting scalar conditional no-go and dispersive relative branch.

The correction is inferred from Einstein's equation and not independently derived from an elastic medium. Curvature and distance effects need not represent local medium stiffness. A null scalar profile on its own is not a dissipative memory mechanism.
