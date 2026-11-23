# Ether v20 — Conditional spin-2 uniqueness and universal source conservation

This is a finite/symbolic test for **necessary conditions** of gravity, not a derivation of gravity from a gel-like medium.

## Files

- `RESEARCH_NOTE_2026-11-23_v20.md`: Japanese report, assumptions and limitations
- `verify_v20.py`: exact 4D spin-2 Fourier-symbol gauge identities, 1+1 stress Ward identity, 0+1 coupled evolution
- `independent_audit_v20.py`: separate 4D tensor implementation and gauge variation tests with several wavevectors/initial states
- `lattice_conservation_v20.py`: spatial lattice and exact local energy-current identity with time-step convergence
- `audit_v20.json`, `independent_audit_v20.json`, `lattice_audit_v20.json`: machine-readable audits
- `*.png`, `*.csv`: numerical evidence
- `SHA256SUMS.txt`: file hash checks

## Run

```bash
python verify_v20.py
python independent_audit_v20.py
python lattice_conservation_v20.py
```

No external source/data downloads are required. All examples use simulated data.
