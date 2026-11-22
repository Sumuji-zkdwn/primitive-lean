# Exact nonlinear 5D vacuum gravity -> 4D Einstein–Maxwell–dilaton

Date: 2026-11-22 JST. Status: independent DRAFT research PR.
This is a reconstruction of known Kaluza–Klein physics, **not**
an original solution or a proof of the full Standard Model.

## Aim and difference from the linearized witness

PR #197 proved that a Kaluza–Klein circle-invariant perturbation
h_{mu,psi}=A_mu of flat five-dimensional vacuum gravity propagates
a source-free U(1) Maxwell wave at linear order. It also showed
that the over-restricted ansatz of a fixed-radius circle, flat
4D metric and a nonzero uniform magnetic field fails the full
five-dimensional vacuum equations.

Here we remove both restrictions. Take an **exact, nonlinear,
non-product, Ricci-flat** five-dimensional Kaluza–Klein monopole
(Gross–Perry–Sorkin/Taub–NUT) and check its complete reduced
Einstein–Maxwell–dilaton (EMD) dynamics.

## Exact 5D metric

Use Lorentzian signature (-,+,+,+,+) and local coordinates
(t,r,theta,phi,psi) with k>0, r>0, 0<theta<pi:

    H(r)=1+k/r,
    ds5²=-dt² + H(r)(dr²+r²(dtheta²+sin²theta dphi²))
                + H(r)^(-1)(dpsi+k cos(theta)dphi)².

Only the 5D Lorentzian metric is a fundamental field here.
The field A below comes from the mixed metric component, and
the scalar phi from its radius. As a global metric, regularity at
the NUT centre requires the standard fibre period 4*pi*k
and correct gauge patches; **the code checks r>0 only**.

Direct symbolic verification does **not** need to assume the
Gibbons–Hawking theorem: tools/check_kk_exact_emd.py computes
the inverse metric, all Christoffel symbols and all 25 components
of the 5D Ricci tensor. Each equals exactly zero for symbolic k.

## Einstein-frame 4D fields and equations

Use the convention

    ds5² = exp(phi/sqrt(3))*ds4_E²
           + exp(-2*phi/sqrt(3))*(dpsi+A)²,

so the exact extraction yields

    ds4_E² = -H^(-1/2)dt²+
               H^(1/2)(dr²+r²(dtheta²+sin²theta dphi²)),
    A = k*cos(theta)*dphi,
    phi = (sqrt(3)/2)*log H,
    F=dA=-k*sin(theta)*dtheta∧dphi.

The convention is important: another popular convention flips
phi and the exponents simultaneously, or rescales A by a factor
of two. Do not mix signs from different conventions.

For this normalization the 4D action (up to constants and a
boundary term) is

    S4 = ∫sqrt(-g) [R - 1/2 (∂phi)²
                   - 1/4 exp(-sqrt(3)*phi) F_mu_nu F^mu_nu].

The equations checked, with indices of g_E, are:

    Ric_mu_nu =
      1/2 ∂mu(phi)∂nu(phi)
      +1/2 exp(-sqrt(3)*phi)
         (F_mu_rho F_nu^rho - (1/4)g_mu_nu F²),

    nabla_mu(exp(-sqrt(3)*phi)F^mu_nu)=0,

    box(phi) + (sqrt(3)/4)exp(-sqrt(3)*phi) F²=0.

Each is a **genuine nonlinear field equation**: no weak-field or
small-k expansion is performed.

## Direct independent evidence

The Python verifier differentiates both the original 5D metric
and the 4D Einstein-frame metric. It checks:

- all 25 5D Ricci components vanish exactly (including off-diagonal);
- metric extraction reconstructs all 5D components;
- all 16 4D Einstein equations exactly;
- all 4 dilaton-weighted Maxwell equations exactly;
- the nonlinear scalar source/wave equation exactly;
- the magnetic field is nonzero, with flux -4*pi*k and normalized
  first Chern number -1 for the appropriate fibre period.

Some exact 4D Ricci components (define Q=r+k) are:

    Ric_tt = k²/[4 r Q³],
    Ric_rr = k²/[8 r² Q²],
    Ric_theta_theta = k²/[4 Q²],
    Ric_phi_phi = Ric_theta_theta*sin²theta.

The scalar gradient is not zero; its radial derivative is

    phi' = -(sqrt(3)/2)k/(r Q).

The 4D source terms include the coupling exp(-sqrt(3)*phi)=H^(-3/2)
and field strength F²=2k²/(H r⁴). The scalar equation works because

    box(phi) = -sqrt(3)*k²/[2*r^(3/2)*Q^(5/2)],
    +(sqrt(3)/4)exp(-sqrt(3)*phi)F²
             = +sqrt(3)*k²/[2*r^(3/2)*Q^(5/2)].

These cancel **only after allowing the circle radius to vary**.
The fibre radius squared is g_psi_psi=H^-1=r/(r+k),
which is not constant for k>0. Setting k=0 recovers the flat vacuum.

## A projection-dependent curvature singularity

The full 5D Riemann-square scalar, independently derived at the
equator from Christoffel and Riemann components, is

    K5 = R_ABCD R^ABCD = 24 k²/(r+k)^6,
    lim_(r->0+) K5 = 24/k^4 < infinity   (k>0).

The 4D Einstein-frame metric, by contrast, has scalar curvature

    R4 = 3 k²/[8 r^(3/2)(r+k)^(5/2)],
    lim_(r->0+) R4 = +infinity.

The four-dimensional projection is curvature singular at the
centre, but this particular five-dimensional curvature invariant
has a finite endpoint. The global smooth Taub-NUT extension
requires a proper U(1) circle atlas and period 4*pi*k; it is
a known external theorem, NOT proved merely by finiteness of K5.

The Python checker independently computes the full curvature
contraction and limits. Lean proves the rational K5 formula's
finite endpoint and the cubic pole coefficient for R4 squared,
not the metric-to-Riemann derivation or analytic limits in the kernel.

## Lean formalization boundary

lean/Research/KKExactEMD.lean proves exact rational identities
obtained from the verified differential geometric equations:
harmonicity H''+2H'/r=0, conservation r²H'=-k,
logarithmic derivative H'/H, secant relations demonstrating
nonconstant fifth-dimensional radius, radial scalar current,
the nontrivial Einstein tt/rr/angular source identities, and
nonzero Ricci curvature for k != 0.

The SymPy checker is responsible for **deriving the Ricci tensor
from the actual metric** and verifying the 4D differential
equations. The Lean module does not claim that a coordinate
Levi-Civita tensor, the logarithm/square-root metric and their
derivatives are fully formalized in Mathlib. The normalized
rational expressions in Lean have a clear link to independently
checked exact expressions but are not substitutes for a fully
kernel-verified metric-to-Einstein computation.

As a result this PR is a hybrid evidence package:
- actual curved Lorentzian geometry: exact independent SymPy;
- component identities, radial consistency, algebraic source balance:
  Lean kernel and axiom audit.

This is stronger physically than just the induced tangent-bundle
Yang–Mills identity of PR #195 and stronger than the linearized
vacuum U(1) wave of PR #197, but it **does not** derive independent
nonabelian SU(2)/SU(3), chiral fermions, quantum physics, a unique
observed gauge coupling, or generic perturbative stability.

## References (existing science, not our discovery)

- Tomizawa, Furugori, Sakamoto, Suzuki (2026),
  "Multirotating black holes with nonaligned angular momenta in 5D
  Kaluza-Klein theory", Phys Rev D 114 104032, 6 Nov 2026.
  Equations (1)-(5) provide exactly this KK normalization and
  all three EMD equations:
  https://journals.aps.org/prd/pdf/10.1103/h1xz-h6z1

- Gibbons–Hawking and Gross–Perry–Sorkin magnetic monopole
  local geometry is standard; PR #181 contains an earlier
  independent local 5D Ricci-flatness check and test-geodesic
  Routh reduction.

- Older Kaluza–Klein magnetic monopole and multidimensional
  Einstein–Maxwell–dilaton constructions:
  https://arxiv.org/abs/hep-th/0607060

The next physical barrier is **not** whether nonlinear magnetic
fields can exist inside pure higher-dimensional gravity: this
example proves they can. It is whether realistic, stable,
nonabelian and chiral low-energy fields can be derived without
independent assumptions or extra fundamental matter.
