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

This supplement proves exact algebraic identities between instantaneous
rate expressions and now also the **actual time derivative** of the relative
energy along the already constructed finite Kerr flow, against any comparison
electric/magnetic curves differentiable at the evaluated time:

- `electricGap_hasDerivAt`: the genuine derivative of the scalar Kerr gap;
- `relativeEnergy_hasDerivAt_physical`: chain rule for physical Maxwell
  component rates, with comparison electric derivative `dEB` and magnetic
  derivative `dHB`;
- `relativeEnergy_hasDerivAt_flow`: specialize the previous theorem to the
  independently constructed `FiniteFlow.flow` using its actual electric and
  magnetic time-derivative theorems.

The comparison displacement rate in the right-hand expression is
`db_i=(1+barE_i²)*dEB_i`. No C¹ smoothness for all time is hidden: each
derivative theorem assumes the required comparison derivatives at the
selected time. The finite matrix is skew, with no bound on its norm.

A continuum convergence theorem further requires a smooth reference solution,
uniform-in-mesh consistency bounds for spatial differences and initial relative
energy, then an integrated Grönwall estimate. Time-discretized splitting needs
an additional, genuinely mesh-uniform stability bound; the current `O(1/n)`
constant grows with the matrix norm. No general periodic nonlinear PDE
existence, weak-solution uniqueness, or viscosity-zero limit is claimed.

## Proposed next formal statements

1. `relativeRateRight_le`: use the retained
   `constitutive_remainder_le_three_gap` and
   `electricGap_nonneg` to bound the relative-energy derivative by
   `3*A*relativeEnergy + sum_i(|deltaE_i|*|rD_i|+|deltaH_i|*|rH_i|)`,
   assuming `|db_i|<=A`. This candidate bound contains no `||Q_N||`.
2. `relativeEnergy_gronwall`: integrate that bound without inserting a
   dimension-dependent operator norm.
3. `centeredDifference_consistency`: for a separately assumed smooth
   periodic reference solution, show `||(r_D,r_H)||_h <= C*h²`.
4. Prove conditional *semidiscrete* convergence. Mesh-uniform stability and
   convergence of the **explicit splitting** remain independent questions.

## Validation status

The repaired source-and-ledger commit
`c6ea299cdf1962958b6234d6bbd4fa5cef5f6f13` passed
the pinned Lean proof/axiom workflow (run `42657056414`) and the
full source/proof integration workflow (run `42657056370`).
The proof-only artifact reports 2,739 total theorems, 3,702 named
declarations, complete `--trust=0` compilation, no warnings or
unexpected axioms, and 42/42 direct Astra proof edges present.
The two earlier unsuccessful attempts were tactic/elaboration errors,
not failures of a separately proved PDE statement. The original finite
flow proofs, retained source modules, verifier algorithms, and `main` remain
unchanged. A subsequent documentation-only commit does not change the
proof-verified source snapshot.
