# Delayed-hardening ether: verification v8

Reproducible three-dimensional **linearized canonical gravity** benchmark,
coefficient-uniqueness derivation, and an experimental curvature-memory coupling.

**Scope:** This does NOT derive Einstein gravity from a gel. The linear spin-2
gauge structure is assumed, and finite-volume tetrahedron gluing is not present.
This is a local finite-difference lattice calculation around a flat background.

## Run

```sh
python -m pip install -r requirements.txt
python verify_v8.py
python derive_coefficients_v8.py
python memory_extension_v8.py
```

The scripts produce JSON audits, CSV trajectories and PNG plots in this folder.
All random seeds are fixed. Odd grid sizes avoid the central-difference
checkerboard zero at the Nyquist frequency; the global zero Fourier mode is not
part of the 'two physical polarizations' count.

Read `RESEARCH_NOTE_2026-11-22_v8.md` for derivations, restrictions and sources.
