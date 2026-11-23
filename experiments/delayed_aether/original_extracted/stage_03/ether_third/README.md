# Delayed-hardening effective-medium model — third verification

**Start:** `RESEARCH_NOTE_2026-11-22_v3.md` (Japanese). This is a *mathematical toy model*, not an empirically verified gravitational theory.

The archive combines a radial corotational Skyrme-like defect, a positive scalar coupling, a nonlinear Maxwell-type memory branch, and damped wave dynamics. It checks: (a) lower-bounded Hamiltonian, (b) non-positive energy derivative due to damping/memory, (c) radial finite-time response after a perturbation, (d) mesh refinement, (e) exact finite-speed wavefront in the vacuum scalar sector, (f) unequal characteristic speeds in the chosen vacuum limits.

```sh
python delayed_hardening_dynamics.py
python causal_scalar_pulse.py
python dispersion_limits.py
python audit_repro.py
```

Requires Python 3, NumPy, SciPy, Matplotlib. The numerical tables and figures are included. The static `Radial` model was carried forward from the previous verification bundle and copied into `radial_profile_positive.py`.

**Limits:** finite radius, radial ansatz, hand-chosen memory and damping, time interval 0..8. No non-radial PDE stability proof, no Lorentz symmetry or equivalence principle, no prediction of actual gravity.
