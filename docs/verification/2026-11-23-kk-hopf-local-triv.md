# Hopf north local trivialization, incremental kernel verification

Date: 2026-11-23 JST. Stacked on draft PR #227, which supplies an actual
Homeomorph for the topological orbit quotient S^3/U(1) ≃ₜ S^2.
This PR builds an **explicit local fibre chart**, not just a quotient equivalence.

## North chart

Let B_N = {b ∈ S² | 1 + b_z > 0}, E_N = proj^{-1}(B_N) ⊂ S³,
and U(1) = {(c,s) ∈ R² | c²+s²=1}.

The north section N(b) is the prior Lean-proved
northVec (b_x,b_y,b_z), with proj(N(b))=b. For X ∈ E_N,
define the phase coordinates

  c(X) = dot4(N(proj(X)),X)
  s(X) = skew(N(proj(X)),X),

where dot4 and skew are real bilinear pairings from PR #225.
Prior Lean orbit completeness ensures X = rotate(c(X),s(X),N(proj(X))),
and the dot/skew identities prove c(X)²+s(X)²=1.

The converse map sends (b,(c,s)) to rotate(c,s,N(b)).
The proof checks base projection, recovery of both phase components,
and both roundtrip identities. Its exported Lean type is
'NorthTotal ≃ NorthBase × UnitPhase'.

## Scope and next steps

Algebraic north-chart bijection is **not automatically a homeomorphism**.
Until checked, it must not be described as a smooth local trivialization,
a principal circle bundle, or a calculation of winding/Chern class.

The next step is to prove continuity of the north section, reconstructed
phase, and both chart directions to upgrade this Equiv to a Homeomorph.
Repeat for the south chart and show the overlap phase on all non-polar
base points. Only then address smoothness and transition degree.

Local CLI check: SymPy 1.14.0 script
tools/check_kk_hopf_north_triv.py checks phase reconstruction and action
polynomial identities independently. The pinned GitHub CI compiles the
Lean source with --trust=0 and audits every theorem and the exported
equivalence; **results must be read from the actual CI run**.

Do not merge; main and earlier draft branches remain unchanged.
