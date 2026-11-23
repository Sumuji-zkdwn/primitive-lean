# Ether / delayed-hardening research: V6

Static gravitational-sector continuation of V5. This is a **toy metric study**, not a successful reconstruction of GR or experimental confirmation of an ether. V6 does not implement the full time-dependent memory/hardening model.

Highlights:

- Flat-background scalar + unit timelike direction disformal metric gives PPN beta=gamma=1 **by construction** in static weak fields.
- Its exterior Ricci scalar is exactly nonzero: `R = -2m^2 exp(-2m/r)/r^4`.
- Optical bending, gravitational redshift and geodesic periapsis shifts compared with isotropic Schwarzschild, including invariant matching (same impact parameter / same circumferential radii).
- A positive scalar-field kinetic action with stress-energy metric coupling yields a toy static source proportional to `exp(2U)*(rho+3p)`, not Einstein equations.
- Seven pressure-supported constant-density toy fluid spheres numerically satisfy their own boundary value problem.
- A pure scalar isotropic spatial deformation has zero transverse-traceless (TT) linear wave modes, so spin-2 GR waves are not restored.
- Imposing GR vacuum equations **externally** fixes the second and third orders of metric potentials, and exposes precisely what was not derived.

Important files:

- `RESEARCH_NOTE_2026-11-22_v6.md`: full Japanese research note with derivations, results, limitations and citations.
- `verify_v6.py`: geodesics, curvature invariant formula, PPN, wave TT test, CSV and plots.
- `compare_invariants_v6.py`: gauge-independent physical comparisons via impact parameter and areal radius.
- `static_star_v6.py`: self-consistent (within the scalar toy equations) static fluid BVP and source integral audit.
- `vacuum_series_v6.py`: order-by-order vacuum GR equations (imposed, **not** derived).
- `audit_v6.py`: full 4D Ricci from Christoffels, scalar action checks, independent 43-digit mpmath geodesic quadrature.
- `results.json`, `audit_v6.json`, `vacuum_series.json`, `static_star_results.json`, `invariant_comparison.json`.

All quantities are in geometric toy units G=c=m=1 unless noted. Real Solar System validation, preferred-frame tests, dynamic tensor gravity and Lean formalization remain outstanding.

Run all via:

```bash
OPENBLAS_NUM_THREADS=1 python verify_v6.py
OPENBLAS_NUM_THREADS=1 python static_star_v6.py
OPENBLAS_NUM_THREADS=1 python compare_invariants_v6.py
OPENBLAS_NUM_THREADS=1 python vacuum_series_v6.py
OPENBLAS_NUM_THREADS=1 python audit_v6.py
```
