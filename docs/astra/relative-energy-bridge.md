# Finite Kerr relative-energy bridge: first additive step toward a continuum limit

Base: `Sumuji-zkdwn/primitive-lean` PR #122, head `5b744532cba43fdd0075f868883cdabaff7d49c3`.
This is an independently authored native proof supplement, not a modified copy
of the retained `kerr-koopman-lean` sources. It leaves `main` unchanged.

## Reused definitions

The original finite system is
`D'=-Q H, H'=-Q g(D)`, with `D(E)=E+E³/3`,
`W(E)=E²/2+E⁴/4`, and `Q(i,j)=-Q(j,i)`.
`KerrKoopman.FiniteFlow.flow` constructs its actual finite solution.
The retained scalar relative energy is
`KerrKoopman.RelativeEnergy.electricGap(barE,E)`:
`W(E)-W(barE)-barE*(D(E)-D(barE))`.

For an actual field `E,H`, comparison field `barE,barH`,
comparison rates `db,dh`, define
`deltaE=E-barE`, `deltaD=D(E)-D(barE)`,
`deltaH=H-barH`, and the comparison residuals
`rD=db+Q barH`, `rH=dh+Q barE`.
The rate expression on the left is

```text
sum_i [deltaE_i*(-Q H)_i
       -deltaD_i/(1+barE_i²)*db_i
       +deltaH_i*((-Q E)_i-dh_i)]
```

The theorem `relative_energy_rate_identity` identifies this exactly with

```text
sum_i [(deltaE_i-deltaD_i/(1+barE_i²))*db_i
       -deltaE_i*rD_i -deltaH_i*rH_i].
```

The equality follows from `FiniteEnergy.skew_pairing`. It is exact for
**every finite skew matrix Q** and does not contain `||Q||`.
The theorem `relative_energy_controls` gives the squared physical field
error bound by the scalar gap, using the original
`RelativeEnergy.square_error_le_gap`; `constitutive_remainder_control`
reuses the original dimension-free nonlinear remainder estimate.

## What is and is not established

This supplement proves algebraic identities between *instantaneous rate
expressions*. Its `actual_flow_relative_rate_identity` instantiates the
algebraic identity with the actual `FiniteFlow.flow` state. **It does not yet
prove a Lean `HasDerivAt` theorem for the time-dependent relative-energy
function**: that chain-rule connection is the next outstanding proof step.

A continuum convergence theorem further requires a smooth reference solution,
uniform-in-mesh consistency bounds for spatial differences and initial relative
energy, then an integrated Grönwall estimate. Time-discretized splitting needs
an additional, genuinely mesh-uniform stability bound; the current `O(1/n)`
constant grows with the matrix norm. No general periodic nonlinear PDE
existence, weak-solution uniqueness, or viscosity-zero limit is claimed.

## Proposed next formal statements

1. `relativeEnergy_hasDerivAt_flow`: connect the genuine finite flow and a
   differentiable comparison curve to the already proved instantaneous identity.
2. `relativeEnergy_gronwall`: derive an estimate uniform in `||Q_N||` from the
   scalar remainder and the skew cancellation.
3. `centeredDifference_consistency`: for a fixed smooth periodic reference
   solution, show `||r_D,r_H||_h <= C*h²`.
4. A conditional *semidiscrete* convergence theorem; only after this, analyze
   the separate explicit Lie-step time discretization.

## Validation status

As initially submitted, these are candidate Lean proofs; a passing
`--trust=0` integrated build and direct proof-value edge audit must be
observed before calling them kernel-verified. Existing Lean proofs, verifier
algorithms, and `main` were left intact; only the new proof, its independent
contract and additive registration/manifest metadata were changed.
