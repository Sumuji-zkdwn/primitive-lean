# Intensity-only exchange symmetry

Date: 2026-11-07. Base: PR #86 exact head `f08c8786f774cc8ad3abd45184ce3cf17ff1ecc5`.

## Lean addition

`lean/DarkBrightIntensity.lean` imports the existing `Spinor`, `mix`, `reQ`,
`imQ`, and `output` definitions. It leaves PR #86's definitions and 28 existing
theorems untouched and does not use any of those theorems in its proofs.

The new module proves:

- Exchange `S(B,D)=(D,B)` fixes `Re Q` and negates `Im Q`, so `Q` becomes its
  complex conjugate and `|Q|²` is unchanged.
- `S` commutes with the supplied mixer for every real `c,s`; no condition
  `c²+s²=1` is needed.
- For every finite list of mixer parameters, the full intensity trace,
  including the initial readout and each post-mixer readout, is identical for
  `x` and `S(x)`.
- The terminal intensity after any finite mixer word is also identical.
- For `B=1,D=i`, the complex observations are `Q=-i` and `Q=+i` after exchange,
  while both intensities equal `1`. The added signed observable `Im Q` separates
  this pair.

No hypotheses beyond the imported model definitions are used. In particular,
unitarity/norm preservation is unnecessary for the exchange argument. The
additional theorems are audited against the standard Lean axiom allowlist;
there are no project-added axioms or `sorry` declarations.

## Exact Python regression

`python tools/check_dark_bright_intensity.py` uses `fractions.Fraction` over
all 625 integer-coordinate states in `[-2,2]^4`. It checks exchange
involution, conjugation, intensity equality, commutation for four real pulse
parameters, and every word of length 0 through 3 over three rational pulses.
These are finite regression results only; they do not stand in for the
universal Lean theorems.

## Minimality convention and observation boundary

There is no smallest nonzero rational amplitude by magnitude: scaling both
amplitudes by any nonzero rational scales `Q` and can make `|Q|²` arbitrarily
small while preserving the ambiguity. The displayed witness is minimal in the
natural discrete convention of Gaussian-integer coordinates: both amplitudes
must be nonzero to make `Q` nonzero, so each has squared modulus at least one;
`B=1,D=i` attains total squared norm `2`. It also uses only coordinates `0`
and `1` and denominator `1`.

The extra `Im Q` readout is an abstract signed coherence quadrature. In a
two-mode polarization realization, an appropriate phase-sensitive
interferometric measurement or signed Stokes quadrature can play that role.
This is a statement about what observable would break the mathematical
exchange symmetry. It is not an optical apparatus design or evidence that the
model's amplitudes are photon constituents. No photon ontology, quantization,
Maxwell dynamics, propagation, or experimental result follows from this
formalization.
