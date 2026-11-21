# Gravity-only reconstruction: geometric charge and exact obstruction ledger

Date: 2026-11-22 (JST). Status: **proposed draft PR**. Python symbolic verification is local-pass; exact-head Lean kernel and GitHub Actions status must be checked separately.

## Goal and scope

The user asks to keep the ambitious goal of reconstructing existing physics from gravity alone. We interpret "gravity" here as **a single higher-dimensional Lorentzian metric and its geometry**, not *only the measured four-dimensional metric*. Under the latter restriction the program already fails for the sign of electric charge (Reissner–Nordström). The reformulation does **not** count a loose analogy as a physical derivation.

Here we reconstruct exact **charged test-particle kinematics** from a single metric; we neither prove pure-vacuum Einstein field equations nor obtain fundamental quantum fermions.

## Algebraic and geometric witness

Use a 2D Lorentzian base with coordinates (t,x), and a one-dimensional fibre y. The full metric is

    ds_hat² = -dt² + dx² + (dy + E x dt)².

Equivalently, the symmetric matrix in (t,x,y) coordinates is

    [[E²x² - 1, 0, Ex],
     [0,          1, 0 ],
     [Ex,         0, 1 ]].

Its determinant is -1 (nondegenerate for all E and x), and its scalar curvature is R_hat = E²/2. Therefore **for E ≠ 0 this illustrative 2+1 metric is not Ricci-flat**, and must not be advertised as a vacuum Einstein solution.

For an affine geodesic with velocity (t_dot,x_dot,y_dot), the Lagrangian is

    L = 1/2 [-t_dot² + x_dot² + (y_dot + Ex t_dot)²].

Since y is cyclic, q := ∂L/∂y_dot = y_dot + Ex t_dot is conserved. Eliminate y_dot = q - Ex t_dot by Routh reduction:

    R_q = (x_dot² - t_dot² - q²)/2 + q Ex t_dot.

The Euler–Lagrange equations give

    t_ddot = q E x_dot,
    x_ddot = q E t_dot.

These match the Lorentz-force equations for a constant electric field in 1+1 dimensions, with q the charge-like conserved fifth momentum. A full computation of all three Christoffel geodesic equations independently confirms these exact identities (tools/check_geometric_charge.py).

The additional *two spectator coordinates* can extend this local toy metric to 5 dimensions, but do not make it Ricci-flat: the scalar curvature remains E²/2.

## Gauge invariance and nonlocal observable

For general potential components (A_t,A_x), the same quadratic form is

    Q = -u_t² + u_x² + [u_y + A_t u_t + A_x u_x]².

It is unchanged under

    (A_t,A_x) -> (A_t+alpha,A_x+beta),
    u_y -> u_y - alpha u_t - beta u_x.

For alpha,beta constant, this is the differential of a local circle-coordinate change y' = y - alpha*t - beta*x. The fibre reflection y -> -y changes A -> -A without changing the full line element; the simultaneous sign change q -> -q preserves projected motion.

For a triangle with oriented edge connection values e01,e12,e20, the sum e01+e12+e20 is unchanged when a local fibre origin at vertex i is shifted by lambda_i. This exact discrete holonomy relation is also formalized in Lean, and provides a candidate observable distinguishing globally nontrivial geometric connections.

## The 4D obstruction and how the route changes

The Reissner–Nordström line element has a coefficient of the form f(r)=1-2M/r+Q²/r² (appropriate units). Substituting Q→-Q leaves the entire metric invariant. Thus, from *that four-dimensional metric alone* no reconstruction map can recover the absolute sign of Q. This is an information-theoretic noninjectivity: a deterministic decoder g→Q cannot assign both signs to the same g. Additional non-gravitational probes or enriched geometry are required.

The higher-dimensional metric has mixed components g_{mu y}; the geometry of the fibration stores a connection and therefore more structure than the original 4D metric. There is still a simultaneous fibre-orientation/sign convention; relative signs matter physically. This is not a counterexample to the no-go, because we have changed the input data.

## Dynamic and quantum frontier: not yet reconstructed

1. Pure higher-dimensional Einstein-Hilbert gravity reduced on a circle yields a lower-dimensional metric, a vector, and a scalar/radion ("dilaton"). A constant-radius truncation with generic nonzero electromagnetic fields is **not** consistent: the omitted scalar equation imposes a condition such as F_{\mu nu}F^{mu nu}=0 in the simplest case. The current kinematic model does not solve the full system.
2. A nonabelian gauge connection can arise by reduction on an internal space with the right isometries, but getting SU(3)xSU(2)xU(1), actual couplings, quantum spectra, symmetry breaking, and anomaly cancellation requires extra hypotheses and detailed calculations.
3. Chiral fermions (and spin/statistics), quantum measurement, and observational correctness are unsolved here. A bosonic classical metric alone does not automatically supply standard-model quantum matter.

## Proposed formal criteria for further work

A candidate "gravity-only" theory must specify one primitive mathematical object, e.g. a smooth higher-dimensional Lorentzian metric (and a dynamics, ideally the higher-dimensional Einstein-Hilbert action). It must then provide operationally defined projection maps from its solutions to: (i) gravitational trajectories, (ii) charged forces and Maxwell-like fields, (iii) nonabelian forces, (iv) chiral quantum matter, (v) experimentally measured parameters. For each, prove covariance and a well-defined dynamical reduction, find an independently falsifiable prediction, and establish a limit compatible with observations.

**Next strictly defined test:** derive and independently check the scalar/radion equation of motion from a 5D Einstein-Hilbert reduction, and either find a nontrivial, fully consistent dynamical sector or produce the minimal counterexample. Do not jump from kinematic covariance to dynamic equivalence.

## Reproducibility

- Lean: lean/Research/GeometricCharge.lean — 12 algebraic theorems on fibre momentum, Routhian, gauge covariance, loop holonomy, charge signs and metric determinant.
- SymPy: tools/check_geometric_charge.py — exact matrix inverse, determinant, Christoffel symbols, three geodesic equations, Routhian, curvature, and charge-sign noninjectivity.
- CI: .github/workflows/geometric-charge.yml — exact-head pinned Lean, axiom audit, SymPy checker. The workflow's pass status must be observed before any claim of Lean validation.

## References

- Overduin & Wesson, "Kaluza-Klein Gravity" (1997), https://arxiv.org/abs/gr-qc/9805018 .
- Gerard 't Hooft, black hole lecture notes (Reissner–Nordström metric), https://webspace.science.uu.nl/~hooft101/lectures/blackholes/BH_lecturenotes.pdf .
- Georgios Douzas, "The Kaluza-Klein reduction," https://georgedouzas.github.io/posts/kaluza-klein-theories/part-iii-01-kaluza-klein-reduction.html .
- Baptista, "Chiral interactions of fermions and massive gauge fields in Kaluza-Klein models," JHEP 05(2026)008, https://arxiv.org/abs/2506.09126 .
