# PR #88 IVP construction and independent trajectory check

Target source: `Sumuji-zkdwn/primitive-lean` PR #88, model commit
`908a626654fa30e74d633bf97636732367d414d3`.

## Initial-value problem

The state is (z=(x_1,v_1,x_2,v_2,y)), with

\[
F=\kappa(gx_1x_2-y),\quad
\dot x_1=v_1,\quad \dot v_1=-\omega_1^2x_1-gx_2F,
\]
\[
\dot x_2=v_2,\quad \dot v_2=-\omega_2^2x_2-gx_1F,
\quad \dot y=F/(2c).
\]

For the requested case, ((\kappa,c,g,\omega_1,\omega_2)=(1,1,1,0,0)) and
(z(0)=(1,0,1,0,0)). Thus (F=x_1x_2-y), and the vector field is polynomial
on \(\mathbb R^5\), hence continuously differentiable and locally Lipschitz.
The Picard–Lindelöf conditions hold on a sufficiently small closed ball and a
sufficiently short time interval.

The new Lean module invokes Mathlib's Picard–Lindelöf existence theorem for
this exact polynomial vector field, translates the resulting \(\mathbb R^5\)
solution into PR #88's `Path`/`SolvesAt`, and applies the existing
`emitted_pos_iff_product_nonzero` theorem. Since (x_1(0)x_2(0)=1), it proves
there is some (T>0) for which the constructed path has positive emitted work.
It also proves the initial first derivatives from the equations:

\[
\operatorname{deriv}x_1(0)=\operatorname{deriv}x_2(0)=0,\quad
\operatorname{deriv}v_1(0)=\operatorname{deriv}v_2(0)=-1,\quad
\operatorname{deriv}y(0)=1/2.
\]

## Taylor jet

Repeated substitution into the polynomial ODE gives the exact rational
coefficients below. These are the local Taylor coefficients; the Lean patch
proves local existence and the initial derivatives, but does not formalize an
analytic remainder bound.

Because the local solution satisfies \(x_i'=v_i\) throughout its interval,
the state-coordinate result \(v_i'(0)=-1\) gives \(x_i''(0)=-1\). The Lean
theorem records the derivative of each state coordinate; it does not separately
prove the second-derivative notation for \(x_i\).

\[
\begin{aligned}
x_1(t)=x_2(t)&=1-\tfrac12t^2+\tfrac1{12}t^3+\tfrac{11}{96}t^4-\tfrac{31}{960}t^5+O(t^6),\\
v_1(t)=v_2(t)&=-t+\tfrac14t^2+\tfrac{11}{24}t^3-\tfrac{31}{192}t^4-\tfrac{73}{384}t^5+O(t^6),\\
y(t)&=\tfrac12t-\tfrac18t^2-\tfrac7{48}t^3+\tfrac5{128}t^4+\tfrac{169}{3840}t^5+O(t^6),\\
W(t)&=\tfrac12t-\tfrac14t^2-\tfrac14t^3+\tfrac3{16}t^4+\tfrac2{15}t^5+O(t^6),
\end{aligned}
\]
where \(\dot W=F^2/2\), (W(0)=0). In particular (F(0)=1), so positive
emission starts immediately; this is stronger for this IVP than merely finding
some later nonzero product.

## Existence through finite times

The Lean proof establishes a nonempty local interval. For this particular
parameter set, the standard continuation argument extends the solution to
all finite forward times: the PR #88 energy identity gives
\(E'(t)=-F(t)^2/2\le0\), while (E(0)=1/2\) and
\(E=(v_1^2+v_2^2+(y-x_1x_2)^2)/2\). Thus \(|v_i|\le1\),
\(|x_i(t)|\le1+t\), and \(|y(t)|\le(1+t)^2+1\) on every finite interval.
The state cannot escape to infinity in finite time, so the polynomial ODE's
usual continuation criterion applies. This global-continuation step is an
analytic argument, not part of the new Lean theorem.

## Numerical check

`tools/check_two_motion_ivp.py` is a self-contained Python standard-library
implementation of classical RK4. It integrates the five state variables plus
(W), computes the PR #88 local energy and force at each requested sample,
uses exact `Fraction` arithmetic for the Taylor coefficients, and performs a
576-case parameter grid. It can be run with:

```bash
python3 tools/check_two_motion_ivp.py
```

A separate SciPy DOP853 run (`rtol=1e-13`, `atol=1e-15`, 257 RHS evaluations)
was used as a second numerical method. The following values are rounded from
that run; the RK4 checker agrees to the displayed digits. The symmetric initial
data and local uniqueness of this polynomial ODE imply \(x_1=x_2\) and
\(v_1=v_2\); the Lean patch does not formalize uniqueness, so the table records
the coalesced numerical values.

| t | x₁=x₂ | v₁=v₂ | y | F | local energy | W | E+W−0.5 |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 0.0 | 1.000000000 | 0.000000000 | 0.000000000 | 1.000000000 | 0.500000000 | 0.000000000 | 0 |
| 0.1 | 0.995094438 | −0.097059622 | 0.048608496 | 0.941604445 | 0.452730036 | 0.047269964 | < 1e−14 |
| 0.2 | 0.980837813 | −0.186646311 | 0.093908766 | 0.868134050 | 0.411665210 | 0.088334790 | < 1e−14 |
| 0.3 | 0.958079668 | −0.266821050 | 0.135222170 | 0.782694480 | 0.377498797 | 0.122501203 | < 1e−14 |
| 0.4 | 0.927830301 | −0.336318292 | 0.172037765 | 0.688831304 | 0.350354276 | 0.149645724 | < 1e−14 |
| 0.5 | 0.891191691 | −0.394566592 | 0.204025885 | 0.590196745 | 0.329848894 | 0.170151106 | < 1e−14 |
| 0.6 | 0.849290298 | −0.441633208 | 0.231035934 | 0.490258075 | 0.315216381 | 0.184783619 | < 1e−14 |
| 0.7 | 0.803218328 | −0.478114509 | 0.253081314 | 0.392078370 | 0.305456207 | 0.194543793 | < 1e−14 |
| 0.8 | 0.753987599 | −0.504997932 | 0.270315491 | 0.298181809 | 0.299479107 | 0.200520893 | < 1e−14 |
| 0.9 | 0.702497608 | −0.523519223 | 0.283003391 | 0.210499498 | 0.296227397 | 0.203772603 | < 1e−14 |
| 1.0 | 0.649517359 | −0.535032685 | 0.291491797 | 0.130381002 | 0.294759577 | 0.205240423 | < 1e−14 |

At (t=1), RK4 with 20,000 uniform steps gives

- (x_1=x_2=0.6495173586991091), (v_1=v_2=-0.5350326848681537);
- (y=0.2914917970879517), (F=0.13038100216351545);
- (E_{local}=0.2947595767398064), (W=0.2052404232602049);
- energy-balance residual (1.13\times10^{-14}).

The DOP853 final residual is (5.55\times10^{-16}). RK4 step doubling gives
(x_1) differences (2.22\times10^{-10}) (100 vs 200 steps) and
(1.39\times10^{-11}) (200 vs 400 steps). Dividing by the RK4 order factor
(2^4-1=15) estimates the 200-step and 400-step errors as
(1.48\times10^{-11}) and (9.25\times10^{-13}), respectively. The much
smaller 20,000/40,000-step differences are at floating-point roundoff and are
not treated as a rigorous error bound.

The parameter grid used \(\kappa\in\{0.25,1,2\}\),
\(c\in\{0.5,1,2\}\), \(g\in\{-2,-1,1,2\}\),
\(\omega_i\in\{0,1\}\), and \(x_i(0)\in\{-1,1\}\), with zero initial
velocities and (y(0)=0). All 576 cases had positive (W(1)); the smallest
was 0.00781866, and the largest sampled balance residual was
(2.06\times10^{-12}). This is a finite numerical search, not a proof.

Boundary cases show why the theorem's hypotheses matter:

- With \(y(0)=1\), \(x_1(0)=x_2(0)=1\), zero velocities and \(\omega_i=0\),
  the path is an exact equilibrium with (F=W=0) despite nonzero product.
  Here the theorem's initial condition (y(0)=0) is absent.
- With \(g=0\) or \(\kappa=0\), the same zero-boundary initial data give
  zero force and zero emission despite nonzero product. These cases violate
  theorem hypotheses.

No numerical counterexample was found within the stated positivity assumptions.

## What is and is not established

- **Lean-proved:** local IVP existence for the polynomial vector field; translation
  into PR #88's `SolvesAt`; initial derivative values; and positive emitted work
  on some positive interval using the existing conditional theorem.
- **Analytic but not Lean-proved here:** global forward continuation from the
  energy bounds, hence exact existence through (t=1).
- **Numerical:** the RK4 and DOP853 trajectories, step-doubling estimates, and
  parameter grid.
- **Still supplied by the model:** the outgoing law \(\dot y=F/(2c)\).
- **Not established:** derivation of that outgoing law from a distributional
  wave equation, a physical mechanism for the channel, or experimental meaning
  of the parameters.
