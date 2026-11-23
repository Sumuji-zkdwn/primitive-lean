# Delayed-hardening aether — Verification 22

Bounded scientific verification of **time-reparametrization** Noether consistency in a spatially homogeneous Bianchi I reduction, coupled to two reversible internal scalar fields.

## Commands

```sh
python verify_v22.py
python independent_audit_v22.py
python volume_ambiguity_v22.py
```

Requires Python, sympy, numpy, scipy and matplotlib. Output CSV and PNG are regenerated.

**Important:** ADM/Einstein–Hilbert gravitational dynamics are used as the **input**; this is **not an emergence of gravitation** from the original aether ansatz, nor a full 4D spin-2 consistency proof. Memory is a reversible field, not irreversible viscosity. See the Japanese technical report for assumptions and counterexamples.

Core files: `RESEARCH_NOTE_2026-11-23_v22.md`, `verify_v22.py`, `independent_audit_v22.py`, `volume_ambiguity_v22.py`, and three audit JSON files.
