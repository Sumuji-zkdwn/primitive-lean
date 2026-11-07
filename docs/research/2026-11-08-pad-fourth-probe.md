# PAD four-layer, fourth probe: exact and numerical follow-up (2026-11-08 JST)

## Scope and provenance

- PR #101 head: `dab79767580cabc4038db1155283c9ff8ce5f8af`.
- PR #103 verified head: `67d6dfa8e2760c3d8e2a164914b803284e1800c1`; GitHub Actions run `42386335158` succeeded.
- New files only: isolated Lean sidecar, independent pure-standard-library Python checker, and CI. Existing PR #101 and PR #103 Lean sources and proofs remain unchanged.
- The model `s_i(alpha)=u_i^alpha` is illustrative; physical PAD/eKE calibration and experimental noise are **not** established.

## Exact fixed-pair result

Read exact positive rational `tripleP` and `tripleQ` from the PR #103 Lean source. Both have mass 1 and mean 3/2.

Set `g(t)=response(t^3,tripleP)-response(t^4,tripleQ)`. Its exact factorization is:

`g(t)=-(t-1)(2t-1)(3t-1)(4t-1)R(t)/3042500`,

`R(t)=41616t^8+86700t^7+119935t^6+128090t^5+138186t^4+147450t^3+84370t^2+12980t+1298`.

All coefficients of `R` are positive. Hence `R(t)>0` for `t>=0`, and the fixed pair has positive coincidence roots **only** at `t=1/4,1/3,1/2,1`.

For the proposed fourth nominal `u=64/125` (`t=4/5`), the exact gap is `13370535881703/371398925781250 ~ 0.036000469989453075` and is strictly positive. The endpoint `u=1` is a fourth distinct, but uninformative, probe: both responses equal the mass. Therefore it is a trivial fourth-probe ambiguity, not an interior four-point ambiguity.

## Fixed alpha pair, stronger conditional exclusion

With *both* mass and mean fixed at 1 and 3/2, respectively, with alpha values `1` vs `4/3`, and four nominal probes `(1/64,1/27,1/8,64/125)`, equality of responses yields four linear equations for `(p2,p3,q2,q3)` using

`[(s-1)^2, (s-1)^2(s+2), -(v-1)^2, -(v-1)^2(v+2)] · (p2,p3,q2,q3) = (3/2)(v-s)`,

where `s=t^3, v=t^4`. Their exact determinant is `-267843667408163/27518828544000000000` (nonzero). The unique candidate has

`p1=-10198519616027/34784891871190 < 0`,

`q1=-442933771561904/434811148389875 < 0`.

Thus **no positive profiles** fit all four points under those specific fixed calibration values. When both alpha values are arbitrary, this result does **not** establish global uniqueness.

## Finite search (not a theorem for continuous alpha)

For each of 7 integer exponent pairs `(a,b)=(6,7),(5,6),(4,5),(3,4),(2,3),(1,2),(2,5)`, exhaust the 70 four-element subsets of rational `t` from `{1/6,1/5,1/4,1/3,2/5,1/2,3/5,4/5}`. Use `u=t^a`, alternate `v=t^b`, exact Fraction elimination, and mean=3/2. All 490 systems are nonsingular; 0 have two strictly positive profiles. This does **not** exclude continuous-grid or arbitrary-alpha counterexamples.

## Distinguish three questions

1. *Fixed-hypothesis discrimination*: `|F_P(u)-F_Q(u^(4/3))|` is about `0.03600047` at `u=0.512`; a numerical grid/refinement finds its maximum around `u=0.739675`, gap `0.05564349`. This is NOT a universal optimal design result.
2. *Local invertibility*: if the unknowns are `(p2,p3,alpha)` and mass/mean are known, at an actual probe `s=u^alpha` the Jacobian row is `[(s-1)^2,(s-1)^2(s+2),(ln u)*s*(p1+2p2*s+3p3*s^2)]`. At `u=0.512` the smallest singular values of the four-probe Jacobian are `0.01980759` (P) and `0.00513892` (Q); at `u=0.740`, `0.02502961` and `0.01226361`; at `u=0.900`, `0.02637834` and `0.01569255`. Nonsingularity is only local, not global.
3. *Noise sensitivity*: for one noisy measurement with hypothetical response noise SD 0.01, the fixed-hypothesis gap is 3.600 SD at 0.512 and 5.564 SD near 0.740. The alpha-derivative is `(ln u)*u^alpha*F'_P(u^alpha)`; at `u=0.512`, it is about -0.254409 (P) and -0.156309 (Q), and at 0.740 about -0.240309 and -0.180294. Real PAD covariance/noise and alpha uncertainty are unknown.

The Lean sidecar certifies only exact rational identities, positive remainder, the fixed-pair separation away from old roots, and the endpoint equality. A general global four-interior-probe injectivity theorem or nontrivial four-interior-probe positive collision for arbitrary alpha is **not established**.

## Independent checks

`python3 tools/check_pad_fourth_probe.py`

The new GitHub Actions workflow compiles dependencies and this sidecar with Lean `--trust=0`, prints theorem axioms, and runs exact Fraction tests. No source in PR #101 or PR #103 is modified.
