# Independent audit: passive delayed gel static obstruction and finite multiwell counterexamples

Date: 2026-11-23 (JST). This is a **separate, read-only mathematical audit** of [PR #183](https://github.com/Sumuji-zkdwn/primitive-lean/pull/183) and its [nonconvex follow-up #217](https://github.com/Sumuji-zkdwn/primitive-lean/pull/217). The original PR branches and `main` are not modified by this audit branch. A passing Python run is **not** a Lean proof and does **not** establish a physical particle.

## Model and scope

Let `B` be the oriented incidence matrix of a finite connected graph, `x` the vertex displacement, `v` the velocity, `h` the edge memory, `epsilon=Bx`, and `delta=epsilon-h`. For `rho,b,gamma>0`, `kappa>=0`, set

```text
g(delta) = b*delta + kappa*delta^3
E = (rho/2)||v||^2 + sum_e[U(epsilon_e) + b*delta_e^2/2 + kappa*delta_e^4/4]
x_dot = v
rho*v_dot = -B^T[U'(epsilon)+g(delta)]
h_dot = gamma*g(delta)
```

The chain rule and incidence cancellation give **for any finite graph**

```text
E_dot = -gamma * sum_e g(delta_e)^2 <= 0.
```

This identity is symbolic in the three-site test, algebraic on an arbitrary finite graph, and no general graph Lean declaration is claimed.

## Original no-go: precise assumptions

PR #183 has `U(epsilon)=a*epsilon^2/2` with `a>0`. At a stationary state `v=0`, `h_dot=0` implies `g=0`. Because `b>0` and `kappa>=0`, each lag `delta=0`. Then `B^T(a Bx)=0`; multiply by `x^T` to obtain `a||Bx||^2=0`. Since the graph is connected, `x` is constant. This proves **absence of nonuniform static equilibria**, not absence of all dynamic localized waves.

More generally the same energy pairing yields a no-go if `z U'(z)>0` for all nonzero `z` (strict radial restoring sign). It does not apply to the nonconvex potential below.

## Multiwell replacement, not an additive tweak

Replace the **entire relaxed edge potential** by

```text
W(z) = z^2*(z^2 - 1)^2
W'(z) = 6z^5 - 8z^3 + 2z
W''(z) = 30z^4 - 24z^2 + 2.
```

Do not retain the original positive quadratic `a*z^2/2` if claiming the exact zero-energy example `x=(0,1,0)`. For a three-site path `B=[[-1,1,0],[0,-1,1]]`, let `x=(0,1,0)`, `h=Bx=(1,-1)`, `v=0`. Then `E=0`, `B^T W'(Bx)=0`, and `h_dot=0`. The reduced displacement Hessian is

```text
H = 8 B^T B = [[8,-8,0],[-8,16,-8],[0,-8,8]]
spec(H) = {0,8,24}.
```

At `b=1` the **full (x,h) potential Hessian** has eigenvalues

```text
0, 5-sqrt(17), 5+sqrt(17), 14-2sqrt(43), 14+2sqrt(43).
```

All nonzero eigenvalues are positive. The zero mode is uniform translation. A positive semidefinite potential Hessian alone is not the same as a dynamical stability theorem, but here linearized relative modes are also strictly stable: if `lambda>0` is a graph Laplacian eigenvalue, local stiffness `c>0`, the characteristic polynomial after clearing the memory denominator is

```text
rho*s^3 + rho*gamma*b*s^2 + lambda*(c+b)*s + lambda*gamma*b*c.
```

All nonzero-shape roots have negative real parts by the cubic Routh–Hurwitz criterion, for positive `rho,gamma,b,c,lambda`. The independent script explicitly checks the three-site `rho=gamma=b=1,c=8,lambda in {1,3}` case. Translation and center-of-mass drift remain neutral; there is no global-attraction claim.

## Finite zero-energy degeneracy (modulo uniform translation)

For a connected graph any configuration with every edge increment in `{0,-1,+1}` is an exact **global** energy minimizer for `W`. Its Hessian is `B^T D B` with `D_ee=W''(epsilon_e)` either 2 or 8, hence `H >= 2 B^T B`; on the translation quotient it is strictly positive. This conclusion holds for **any finite connected graph**, not just the enumerated small cases.

Fix one vertex to `x_0=0`. Enumerate a spanning tree's assignments in `{-1,0,1}` and reject assignments inconsistent with non-tree edges. Result:

| vertices | path P_n | cycle C_n | complete K_n | path one-site-spike smallest positive Hessian eigenvalue |
|---:|---:|---:|---:|---:|
| 4 | 27 | 19 | 15 | 2.242753313265 |
| 5 | 81 | 51 | 31 | 1.107182188231 |
| 6 | 243 | 141 | 63 | 0.677041534004 |
| 7 | 729 | 393 | 127 | 0.463552721778 |
| 8 | 2187 | 1107 | 255 | 0.340162994415 |

Exact count formulas: `P_n: 3^(n-1)`; `C_n: sum_{j=0}^{floor(n/2)} n!/(j!^2*(n-2j)!)` (central trinomial coefficient); `K_n: 2^n-1`. For the 8-site 3D cube (12 edges), enumeration gives **495** states and a one-site-spike smallest positive Hessian eigenvalue **4.529775788881**.

These are ground-state degeneracies, **not** counts of all positive-energy local minima; a finite spectral gap does not give a size-independent gap as `n -> infinity`.

## Pinned positive-energy metastability

For the pinned three-site chain `x=(0,s,0)`, let `U_a(z)=W(z)+a*z^2/2` and `V_a(s)=2U_a(s)`. If `0<a<2/3`, define `d=sqrt(1-3a/2)` and `s_+^2=(2+d)/3`, `s_-^2=(2-d)/3`. The positive-energy minimum `s_+` and separating maximum `s_-` satisfy

```text
Delta_E = V_a(s_-) - V_a(s_+) = (8/27)*d^3.
```

At `a=0.1`, `s_+=0.986906690241`, `V_a(s_+)=0.098716847575`, and `Delta_E=0.232195934480`. These are **pinned one-degree-of-freedom** results, not free-boundary/global barriers.

## Transient hopping is not autonomous particle transport

A numerical integration with pinned four-site path `x=(0,u,v,0)`, `rho=b=1`, `gamma=5`, `kappa=0`, starting at `(u,v)=(1,0)`, uses initial velocity `s*(-1,1)/sqrt(2)`. With `s=0.7` the trajectory relaxes near `(1,0)`; with `s=1.4` it relaxes near `(0,1)`. This is a reproducible numerical example, not a theorem about all energies or an isolated freely travelling particle.

If energy returns exactly to its initial value over a period, the dissipation integral forces `g(t)=0` at all times, so `h` and `Bx` remain constant. Therefore **nontrivial periodic relative-shape motion** is excluded for this passive system. Uniform drift is not excluded.

## Independent reproduction

```sh
python -m pip install numpy scipy sympy
python -B tools/audit_passive_gel_independent.py
```

The audit script uses symbolic algebra for the 3-site identities and pinned barrier, exhaustive finite assignment enumeration for graph counts, numerical eigenvalues for finite Hessian gaps, and SciPy DOP853 for two time evolutions. It does **not** import the existing `check_passive_gel_delay.py`, `check_passive_gel_multiwell.py`, or `check_passive_gel_mobility.py` modules.

At submission, the script passed in the independent local environment. Whether the proposed PR's exact-head GitHub CI passes must be checked **after** the workflow runs. The general finite-graph proof, numerical results, and Lean kernel certificates are separate evidence categories.

## Physical boundary

No inference is made that these static local minima are elementary particles, have emergent inertial/gravitational masses, obey Lorentz invariance, recover Einstein gravity, or persist as moving solitons. The positive-energy metastable example requires pinned endpoints. New theory claims must be tested separately.
