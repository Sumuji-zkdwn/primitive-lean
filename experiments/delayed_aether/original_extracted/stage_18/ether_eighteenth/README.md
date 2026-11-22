# Ether v18 — non-spherical perturbations and constraint data

**Model status:** This work reproduces and tests a Skyrme/χ matter model coupled to Newtonian self-gravity and to the *existing* Einstein Hamiltonian constraint. It does not derive Einstein gravity from a medium.

Input: `../ether_seventeenth/verify_v17.py` defined the radial `compact_initial()` hedgehog profile and matter couplings. `verify_v18.py` implements the same analytic profile without external file dependencies.

Reproduce from this directory (NumPy/SciPy/Matplotlib):

```
python verify_v18.py
python nonaffine_v18.py
python constraint_v18.py
python collective_mode_v18.py
python independent_audit_v18.py
python figures_v18.py
```

Scripts:

- `verify_v18.py`: exact affine formula + 3D quadrature, weak Newtonian self-binding by isolated linear FFT convolution, far-field quadrupole.
- `nonaffine_v18.py`: 45 localized non-affine quadrupole tests and Jacobian validity.
- `constraint_v18.py`: nonlinear Einstein Hamiltonian *initial-data constraint*, conformally flat K=0 time symmetric, multipole finite-box boundary.
- `collective_mode_v18.py`: restricted 1-DOF quadrupole-mode ODE and reduced energy audit. No dynamic memory field or gravitational radiation.
- `independent_audit_v18.py`: direct finite-difference field derivatives and inertia, brute-force Newton kernel, symmetry and multipole checks.
- `figures_v18.py`: figures built from numerical CSVs.

Research note: `RESEARCH_NOTE_2026-11-22_v18.md` (Japanese).

**Assumptions/limitations:** fixed hedgehog radial seed; Newtonian approximation for binding energy; initial-only nonlinear Einstein constraint; no complete 3+1 field evolution or arbitrary-mode stability proof; `χ` does not have dissipative delayed dynamics in v18.
