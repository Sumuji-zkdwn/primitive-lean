# Planar synchronization and projective locking

These scripts reproduce two constructed mathematical models. They use synthetic
inputs, not celestial observations or quantum experiments.

## Verification

From the repository root:

```bash
python -m pip install numpy==2.3.5 scipy==1.17.0
python -B -X utf8 tools/verify.py --planar-sync-only
```

This uses the existing pins in `lean/lean-toolchain` and
`lean/lake-manifest.json`. It runs both numerical programs, freshly compiles
`PlanarSyncMoments` and `ProjectiveLock` with `--trust=0`, and audits every owned
theorem using the repository's existing standalone-module checker. The checker
discovers source files through `git ls-files`; new local Lean files must be staged.

Numerical checks alone are available without Lean:

```bash
python -B -X utf8 tools/verify_planar_sync.py --numerical-only
```

That route explicitly records `passed: false` for the combined proof claim and
`status: numerical_passed_lean_not_run` when the requested Python checks succeed.

Reports and logs are written below `verification/planar-sync/` and
`verification/planar-sync-kernel/`. Each full invocation uses a fresh output
directory, records the source hashes, and rejects modified verification inputs.

## Files

- `check_moments.py`: exact rational checks of finite point updates, independent
  direct-versus-reduced simulation, explicit failed reductions, and a nonlinear
  contraction-bound example.
- `check_projective.py`: exact rational identities and comparison of phase
  integration with homogeneous linear evolution, including the chart boundary.
- `make_figure.py`: optional illustration of the common-deformation example;
  requires Matplotlib and a Japanese font. It is not a proof dependency.

The figure script writes `verification/planar-sync/shape-sync-geometry.png`.

## Scope

Point correspondences, coordinate systems, and update inputs are supplied. The
moment recurrence predicts discrepancy moments, not future images. The
projective model assumes its first-order evolution law; it does not derive
physical torques or replace a second-order inertial model.

See the [research note](../../docs/research/2026-11-22-planar-sync-projective-lock.md)
and [formalization and verification record](../../docs/verification/2026-11-22-planar-sync-projective-lock.md).
