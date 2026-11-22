# Delayed-aether research sources, stages 11–30

These files preserve the **original Python source scripts** generated during the staged exploratory calculations in the conversation of 2026-11-22–23. They are research evidence, not a stable package or proof of emergent gravity.

See the [v11–v30 evidence ledger](../../../docs/research/2026-11-23-delayed-hardening-ether-v11-v30-index.md), individual [research notes](../../../docs/research/delayed-aether/), and earlier [v1–v10 ledger](../../../docs/research/2026-11-22-delayed-hardening-ether-v1-v10.md). This branch is **stacked on draft PR #193**; it does not update `main`.

## What is preserved

- Original `verify_v11.py`–`verify_v17.py` and `verify_v19.py`–`verify_v30.py` (19 scripts) as UTF-8 source with names unchanged.
- The v18 research note is archived, but **no `verify_v18.py` existed** in the source artifacts; only numerical output/figures were available. No replacement script is fabricated.
- Some stages had additional helper/independent-audit scripts and CSV/JSON/figures. **Those are not all included** here. The original ZIPs generated in conversation remain separate and cannot be reconstructed solely from this repository.
- Code from each stage may assume a particular original working directory, module imports, or generated data. The scripts are retained as a record; no claim is made that all 19 run unmodified in the current CI.

## Reproducing a stage

The original computation environment used approximately these Python packages: NumPy 2.3.5, SciPy 1.17.0, SymPy 1.14.0, Matplotlib 3.10.8, JAX/JAXlib 0.9.0.1, mpmath 1.3.0. These are **observed versions, not dependency lockfiles**; they are not a validated cross-platform environment. JAX stages may need architecture-specific wheels. Start with `python verify_vNN.py --help` only if the source has CLI support; consult its original research note and code before running.

For continuous integration, use the *small independent* standard-library finite checker and the pinned Lean proof file rather than pretending the full historical computations are reproduced.

## Verification status

The stage notes describe historical numerical tests and assumptions. The new GitHub transfer itself verifies only content retention and tests run at the new PR head. No independent recomputation of every original simulation or symbolic computation is implied by the transfer. In particular, the use of Einstein–Hilbert, ADM, Regge, Fierz–Pauli, Skyrme and scalar–tensor actions is explicitly noted; **the original delayed-gel idea has not been shown to derive gravity**.
