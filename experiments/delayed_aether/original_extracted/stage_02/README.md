# 3D ether-like effective-medium toy model — verification bundle

Start with `RESEARCH_NOTE_2026-11-22.md` (Japanese), then run:

```bash
python ether_skyrme_gravity.py
python rank_one_counterexample.py
python radial_profile_positive.py
python positive_pair_force.py
python audit_models.py
```

Requires NumPy, SciPy, Matplotlib. Output CSV/PNG are provided and reproducible.

**Scope:** Static radial variational approximations, exact scaling/no-go calculations,
far-field interaction of frozen dressed sources. Not the dynamical delayed-hardening
model, not a new gravity theory, and not full 3D stability or equivalence principle.

Linear `-g*h*rho2` coupling is **unbounded below** (proof in report); replace it with
positive `rho2*(1-g*h+g^2*h^2/2)` for physically sane test calculations.
