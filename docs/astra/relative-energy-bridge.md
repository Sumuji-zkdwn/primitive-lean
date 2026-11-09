# Finite Kerr relative-energy bridge: dimension-independent growth rate

This additive, repository-native Lean supplement extends Astra PR #122
(base head `5b744532cba43fdd0075f868883cdabaff7d49c3`).
It leaves the original Kerr sources, the established finite-flow proofs,
all verification algorithms, and `main` unchanged.

## Exact finite equations and reused structure

The physical Kerr law and energy are

```text
D(E)=E+E^3/3,    W(E)=E^2/2+E^4/4,
D'=-Q H,        H'=-Q E,         Q(i,j)=-Q(j,i).
```

`KerrKoopman.FiniteFlow.flow` supplies an **actually constructed,
unique global finite-dimensional solution**. Let its restored fields
be `E,H`, and let `barE,barH` be differentiable comparison fields.
Use `barD=D(barE)`, `db=barD'`, `dh=barH'` and residuals

```text
rD=db+Q barH,       rH=dh+Q barE.
```

The scalar gap is the existing `RelativeEnergy.electricGap(barE,E)`:

```text
G(barE,E)=W(E)-W(barE)-barE*(D(E)-D(barE)).
```

The finite relative energy is
`R=sum_i[G(barE_i,E_i)+(H_i-barH_i)^2/2]`.
Existing Lean theorems provide `(E_i-barE_i)^2 <= 2*G(barE_i,E_i)`
and the precise global Kerr nonlinear remainder bound.

`relative_energy_rate_identity` uses `FiniteEnergy.skew_pairing`
to cancel the two skew-difference pairings **exactly**:

```text
R' = sum_i [(deltaE_i-deltaD_i/(1+barE_i^2))*db_i
            - deltaE_i*rD_i - deltaH_i*rH_i].
```

This is a genuine derivative of the constructed finite flow: the
`electricGap_hasDerivAt`, `relativeEnergy_hasDerivAt_physical`, and
`relativeEnergy_hasDerivAt_flow` proofs connect the algebraic identity
to the existing componentwise ODE derivative certificates.

## New Lean theorems: residual growth without ||Q||

The new `relativeRateRight_le` theorem assumes only `A >= 0`
and `|db_i| <= A`, and proves

```text
sum_i rateRight_i
  <= 3*A*R + sum_i[|deltaE_i|*|rD_i|+|deltaH_i|*|rH_i|].
```

`relativeRateRight_quadratic_le` uses scalar Young inequalities
and the proven gap coercivity to obtain the stronger estimate

```text
sum_i rateRight_i
  <= (3*A+1)*R + (1/2)*sum_i[rD_i^2+rH_i^2].
```

`relativeEnergy_deriv_le_flow` applies this bound to the **actual**
finite Kerr flow and the actual comparison derivatives, so the final
result is not an assumed trajectory or a separate evolution axiom.

A mesh weight `h>0` can be multiplied through the validated
unweighted theorem to give

```text
R_h = h*sum_i[G(barE_i,E_i) + (H_i-barH_i)^2/2]
R_h' <= (3*A+1)*R_h + (h/2)*sum_i[rD_i^2+rH_i^2].
```

**The coefficient 3*A+1 is independent of the dimension and ||Q||.**
The residuals `rD,rH` still contain `Q` and require separate spatial
consistency bounds; these do not follow automatically.

## Integration boundary — not yet Lean verified

If `R_h` and the comparison curve have the above derivatives for all
times `0 <= t <= T`, the comparison rate bound is uniform, and
`||(rD,rH)(t)||_h <= B*h^2`, standard scalar Grönwall implies

```text
R_h(t) <= exp((3*A+1)*T)*(R_h(0)+B^2*T*h^4/2).
```

This integrated inequality is **a conditional mathematical deduction,
not yet a Lean theorem**. With `R_h(0)=0`, coercivity would then give
an `O(h^2)` discrete `L2` error in physical `E,H`.

A full semidiscrete limit still requires a separately established
smooth periodic reference PDE solution, uniformly bounded time
displacement rate and third spatial derivatives, consistency of the
centered difference, and identification of initial data. No general
nonlinear PDE existence, post-shock uniqueness, weak-solution limit
or zero-viscosity result is claimed. The explicit Lie splitting
additionally requires mesh-uniform time stability: PR #122's fixed-Q
`O(1/n)` estimate alone does not establish it.

### Independent Fourier consistency check

For the periodic centered difference `(Q_Nf)_j=(f_{j+1}-f_{j-1})/(2h)`,
`h=1/N`, and `f(x)=sin(2*pi*x)`, direct discrete Fourier calculation
gives, for `N>=3`,

```text
||Q_N f_N - (f')_N||_h
   = |N*sin(2*pi/N)-2*pi|/sqrt(2)
   <= (2*pi)^3/(6*sqrt(2)*N^2).
```

The identity, its order `O(h^2)`, and direct finite numerical values
for N=8,16,32,64,128 were checked independently. This one smooth
Fourier mode is not a general smooth nonlinear PDE convergence proof.

## Exact verification provenance

The code-and-ledger commit
`91a8521657865942473a91cae5e57d2f308710bf` passed:

- [Pinned Lean proof and axiom audit — success](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/42661578093)
- [Full source/proof integration — success](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/42661578280)

The verified source includes **2,742 Lean theorems / 3,705 named
declarations** across the joint assembly, `--trust=0`, no warnings,
compile errors or unexpected axioms, and **47/47** direct Astra proof
dependency edges. The relative-energy native bridge now contains
**12 theorems / 15 named declarations**, and the Astra manifest
records **222 added theorems**.

Historical CI attempts that failed due to local Lean elaboration
or tactic issues remain distinct from these successful runs. No
general PDE theorem was counted as proved. Edits to this explanatory
document after the verified commit are documentation only.

## Next theorem

The next Lean target is a scalar `relativeEnergy_gronwall`
integration theorem that consumes `relativeEnergy_deriv_le_flow`
and a uniform residual bound, preferably reusing pinned Mathlib
`le_gronwallBound_of_liminf_deriv_right_le`. Then prove a general
smooth-reference `centeredDifference_consistency` and a conditional
semidiscrete `O(h^2)` convergence theorem. Keep the explicit time
splitting as a separate stability problem.
