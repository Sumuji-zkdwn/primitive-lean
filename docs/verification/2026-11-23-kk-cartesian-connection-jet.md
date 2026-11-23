# Cartesian KK metric-to-first-connection bridge

Date: 2026-11-23 JST. Companion to draft PR #215 (radial KK/EMD) and
#199 (exact one-centre nonlinear KK monopole).

## What has and has not been formalized

This addition is a small, genuinely new **kernel-checked algebraic layer**
toward a differential-geometric Lean proof. It handles the complete 5x5
matrix of a local 5D metric and its polynomial-scaled inverse, then
uses a first-derivative jet table and the coordinate Christoffel sum
to certify individual Levi-Civita connection coefficients.

The 5D metric is the already verified known Cartesian Gibbons-Hawking
witness on a *local* open set H>0:

    coordinates (t,x,y,z,psi)
    H=1+a*z, U=a*x
    ds5²=-dt²+H(dx²+dy²+dz²)+H^-1(dpsi+U dy)².

Writing M=H G and N=H G^-1 gives the polynomial 5x5 matrices

    M=diag(-H, H², H²+U², H², 1) with M[y,psi]=M[psi,y]=U
    N=diag(-H, 1, 1, 1, H²+U²) with N[y,psi]=N[psi,y]=-U.

The first Lean theorem proves all 25 entries of M N = H² I for
arbitrary rational H,U. Another Lean theorem proves that the
normalized G and G^-1 themselves multiply to the identity for H!=0. The condition H!=0 is required when the
scaled matrices are interpreted as the original metric and inverse.
This is a real 5x5 matrix multiplication, not an asserted tensor
value or a numerically checked equality.

## First derivative jet and connection

The original metric has only x- and z-derivatives. The finite jet
tables set dxG and dzG from ∂xU=∂zH=a, ∂xH=∂zU=0. The independent
SymPy oracle starts from the *unscaled* metric, differentiates each
of its 25 entries with respect to each of the five coordinates,
and checks all 125 first partials exactly against these tables.

Lean takes the jet tables as finite algebraic definitions and uses

    Gamma^i_jk := (1/2) sum_m G^im
         (d_j G_mk + d_k G_mj - d_m G_jk)

to prove lower-index symmetry (torsion-free expression) and five
nontrivial Christoffel identities, including

    Gamma^z_{psi psi} = a/(2 H³)
    Gamma^x_{y psi}   = -a/(2 H²)
    Gamma^z_{y psi}   = a U/(2 H³)
    Gamma^z_{xx}      = -a/(2 H)
    Gamma^z_{zz}      = a/(2 H).

The SymPy oracle independently constructs Christoffels from the
original metric and recomputed inverse and verifies these five
coefficients, all 125 Gamma(i,j,k)=Gamma(i,k,j) symmetries, and
the nonzero Riemann component R^x_(z x z)=a²/(2H²).

## Verification and exact boundaries

Run:
    python -B tools/check_kk_cartesian_jet.py

The new dedicated workflow pins the repository Lean toolchain and
SymPy==1.14.0, builds with --trust=0, audits theorem axioms, and
saves source SHA256 values and logs.

**Lean formalizes** finite 5x5 matrix algebra and the connection
as a contraction of stipulated first jets. **Lean now also proves selected analytic derivatives** for
H(z)=1+a*z, G[psi,psi]=H(z)^-1 (dz), and G[y,psi]=a*x/H(z) (dx)
using HasDerivAt. The remaining entries in the 125-component jet
table are still checked by SymPy rather than by Lean.
It does not formally compute a Riemann or Ricci tensor, derive a
general Gibbons-Hawking theorem, or prove global fibre patching.

The next bridge should use HasDerivAt / fderiv for all remaining
metric jet entries, then extend the connection calculation to
second derivatives, Riemann curvature and Ricci. This is known
classical geometry, not a discovery of new physical interactions.

## Lean calculus bridge (subsequent commit)

The following statements are also targeted by the dedicated pinned
Lean/axiom workflow (pending a successful run on the new head):

- `metric_inverse_product`: exact 5x5 rational G*G^-1=I for H!=0;
- `affine_H_hasDerivAt`: real analytic first derivative H'=a;
- `fibre_metric_dz_hasDerivAt`: (1/H)'=-a/H²;
- `mixed_metric_dx_hasDerivAt`: d_x(a*x/H)=a/H at fixed z.

They are meaningful partial derivatives of actual metric functions,
not just jet coefficients stipulated as definitions. They still do
not prove all 125 partials or Ricci tensor construction in Lean.
