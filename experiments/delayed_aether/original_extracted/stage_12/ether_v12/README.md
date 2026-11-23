# v12: self-coupled localized field, geometry and memory

This package is a finite-dimensional mathematical experiment, **not a derivation of general relativity**.

- `verify_v12.py` — self-coupled dynamic field `q∈S³`, scalar intrinsic metric variable `b`, memory variable `z`; same semidiscrete action, Rayleigh dissipation for memory; optional edge-admissibility barrier.
- `verify_v11.py` — included helper for finite tetrahedral meshes, degree and Regge curvature. Bundled from the previous iteration for reproducibility.
- `topology_slip_v12.py` — reproduces a concrete tetrahedron/time interpolation with a zero of the unnormalized spatial field in the unprotected model.
- `audit_v12.py` — variational gradient, time reversal, finite-time topology, coupled/uncoupled controls, energy convergence and interpolation witness.
- `plot_v12.py` — recreates plots from included CSV and NPZ files.
- `*_timeseries.csv` / `*_audit.json` — records of completed runs, with numerical errors.
- `RESEARCH_NOTE_2026-11-22_v12.md` — equations, exact conditional theorem and limitations (Japanese).

Quick start from the extracted directory:

```
python verify_v12.py --n 12 --dt .002 --T .24 --label test
python verify_v12.py --n 12 --dt .0008 --T .6 --s-cut .35 --barrier .1 --label protected_test
python audit_v12.py
```

The last command checks the shipped baseline results, not the `test` files.

**Time integration:** projected force kicks interspersed with exact unit-sphere kinetic drifts (symmetric splitting), with memory damping implemented as a symmetric exponential split.

**Boundaries:** non-periodic spatial cube, fixed vacuum q and zero b,z on the boundary. Initial center position and tangential velocity are specified once; no imposed trajectory thereafter.

**Unresolved:** propagation relative to a Lorentzian metric; tensor gravity; nonperturbative geometric admissibility of all tetrahedra for all time; physical basis for the edge barrier; asymptotic particle localization.
