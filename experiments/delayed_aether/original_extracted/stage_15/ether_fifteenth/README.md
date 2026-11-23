# Ether / delayed-hardening research: v15 independent verification

## Scope

This package extends the previous v14 **by benchmarking nonlinear general-relativistic constraints** and constructing an explicit counterexample to adding delayed curvature naively. All Einstein equations are **assumed from standard GR as a benchmark**. Gravity has **not** been derived from the proposed ether.

### Run

```bash
python verify_v15.py
python evolve_v15.py
python conserved_memory_v15.py
python plot_v15.py
python audit_v15.py
```

Needs Python 3.11+, numpy, sympy, matplotlib. No data downloads. The standalone main verification processes 12 periodic 2D grids (the third spatial dimension is flat), with max n=192. Calculation is finite and generally completes promptly on an ordinary CPU.

### Primary outputs

- `RESEARCH_NOTE_2026-11-22_v15.md`: definitions, exact families, numerical results, error bounds, and limitations (Japanese)
- `graph_constraints.csv`: 3 sample times, 4 resolutions, nonlinear vacuum Hamiltonian and momentum residuals, both ADM evolution residuals, and naive memory obstruction
- `kasner_benchmark.csv`: exact non-diagonal anisotropic Kasner metrics, ADM algebraic checks, and positive exponential spatial metrics
- `kasner_IVP_convergence.csv`: true initial-value RK4 evolution with dt refinement
- `conserved_memory_v15.json`: exact scalar stress-tensor Noether conservation in 1+1 (not coupled gravity)
- `independent_audit_v15.json`: structured PASS assertions
- `constraint_convergence.png`, `memory_constraint_obstruction.png`, `kasner_IVP_convergence.png`, `intrinsic_curvature_slice.png`

### Critical limitations

1. The graph foliation has intrinsic 3-curvature but the underlying 4-spacetime is flat Minkowski, hence it is **not a gravitational field**.
2. The inhomogeneous graph solution is evaluated at a set of exact times, rather than integrated from a single initial state. The Kasner case *is* numerically time-evolved from its initial data, but is spatially homogeneous.
3. The naive memory modification `K'=K+eps*(K-K_past)` is intentionally off-shell; it is a counterexample, **not a realistic viscoelastic material theory**.
4. The covariant two-scalar example is reversible, not dissipative, and has no coupling to the Skyrme-like q field in v14. No long-time topological stability or emergent Einstein theory is claimed.
5. Lean formal verification and GitHub repository updates have not been performed.
