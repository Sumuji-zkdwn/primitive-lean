# Contest economy: conditional self-limitation model (2026-11-05)

Source: lean/ContestEconomy.lean
Independent arithmetic checks: tests/test_contest_economy.py
Dedicated verification: .github/workflows/contest-economy.yml

## The precise claims

1. **Selection does not manufacture objective value.**
   Let q_i lie in [m,M]. For any chosen candidate j and any nonnegative
   baseline weights w_i with sum 1, the excess q_j - sum_i(w_i q_i)
   is bounded above by M-m. Scores, ranking algorithms and selection
   procedures can be arbitrarily complicated without changing this bound.
   This says nothing about whether new scoring criteria reveal previously
   *unmodeled* components of objective value.

2. **Delayed compression can overrun a participation threshold.**
   Write z_t = D_t - D_c, and, while participation remains positive,
   z_(t+1) = a z_t - gamma z_(t-1), with 0<a<1, gamma>0 and
   z_(-1)=0, z_0>0. Under a²<4 gamma, the positive ratio
   r=z_t/z_(t-1) strictly decreases on every valid positive step:
   a-gamma/r<r. This local strict inequality is machine-formalized. More strongly,
   if z_0>0, z_1=a*z_0, a>0, and a²<4 gamma, Lean now proves that
   some finite n satisfies z_n<=0. The proof uses a uniform bound:
   each positive ratio loses at least δ=(gamma-a²/4)/a>0 per step.
   Consequently an infinite all-positive trajectory is impossible.
   The stronger easy-to-check condition a²<=2 gamma additionally forces
   crossing by step 3.

3. **The boundary of the participation model is singular.**
   In the selected symmetric two-person participation equilibrium,
   with objective gap D>0 and net cost e=c-h>=0, let
   p(D,e)=max(0,1-e/D). For each D>0,
   p(D,0)=1 while p(D,D)=0. Lean proves that these contrasting
   paths occur arbitrarily close to (0,0), and gives a direct
   epsilon-delta proof that no common two-variable boundary limit exists.
   Lean also proves the two inner one-sided limits via explicit
   epsilon-delta certificates: for fixed e>0, p(D,e) is eventually
   identically 0 as D approaches 0; for fixed D>0, p(D,e) approaches 1
   as e approaches 0. Thus the iterated limits are respectively 0 and 1,
   while the joint limit does not exist.
   The expression is not a probability when e<0; the model is restricted
   to e>=0 here. At e<0 the underlying game has full participation.

4. **Exact negative-discriminant probe.**
   For a=7/10, gamma=3/20, z_0=9, and z_(-1)=0, all arithmetic is rational:
   z_6=3141/1000000 > 0, z_7=-106533/10000000 < 0.
   The threshold is crossed on step 7. This is verified independently
   in Python and formulated as an exact Lean theorem.

## Derivation from the two-person all-pay participation game

Let the prize for entry depend on the objective gap: R=kappa D.
If the rival stays out, an entrant receives R; if both enter, the
symmetric all-pay equilibrium dissipates the prize in expectation.
Entry has additional fixed cost c, outside option payoff -h, and
the opponent enters with probability p. Thus entry payoff is
(1-p)R-c and outside payoff is -h. For 0<=h<c and R>0,
indifference gives p=max(0,1-(c-h)/R), choosing the symmetric
mixed equilibrium when it exists. A small net cost e=c-h then yields
the expression above after absorbing kappa into D.

These are deliberately strong modeling assumptions. The main social
conclusion does not follow for an economy as a whole merely because
one chosen competition becomes uninformative. The organizer may be
compensated for non-selection output, finance may replenish, the
participant population may renew, and exit may be structurally costly.

## Distinctions and pending obligations

- A high score is not identical to actual economic value; the bound
  applies to modeled objective quality q, not to arbitrarily revised q.
- An arbitrary ranking still exists when the range of q collapses;
  the proof only bounds the *gain from selection*.
- The first Lean theorem assumes finite participants and normalized,
  nonnegative baseline weights, not uniform weights only.
- The sharp recurrence condition a²<4 gamma is proved for the stated
  linear, constant-coefficient recurrence; no theorem says an empirical
  market follows this recurrence or maintains a fixed critical gap.
- A two-dimensional non-limit does not by itself prove that actual
  population participation switches discontinuously at a fixed date.
- No market-wide general equilibrium, credit, labor supply, or institutional
  replacement theorem is claimed.

## Reproducibility

Pinned versions: Lean 4.30.0-rc2; mathlib4 commit
5450b53e5ddc75d46418fabb605edbf36bd0beb6.

From repository root:

    cd lean
    lake env lean --trust=0 ContestEconomy.lean
    cd ..
    python tests/test_contest_economy.py

See the dedicated CI and its exact-head run for kernel validation.
Local authoring without a Lean executable is not itself verification.
