# General GH, KK/EMD, and smooth one-centre Taub--NUT: proof dossier

Date: 2026-11-23. Purpose: distinguish classical mathematical derivations,
independent exact symbolic checks, and the actual Lean kernel theorem boundary.
This is **not** a claim that the three global geometric theorems are all
formalized in Lean.

## 1. General local Gibbons--Hawking theorem

Let U be an oriented open subset of Euclidean R^3, V:U->(0,infinity)
be a smooth harmonic function, and let pi:P->U be a local circle
trivialization with a connection Theta=dpsi+A such that
F=dA=*3 dV. Since d(*3dV)=(Delta V) dx wedge dy wedge dz=0,
A exists on every contractible patch by the Poincare lemma.

The four-dimensional metric is

    g=V (dx^2+dy^2+dz^2)+V^-1 Theta^2.

The three 2-forms (i,j,k cyclic)

    Omega_i=Theta wedge dx_i - V dx_j wedge dx_k

are (anti-)self-dual, of equal constant norm, and satisfy the
quaternionic algebra. Their exterior derivatives vanish because

    dOmega_i=F wedge dx_i - dV wedge dx_j wedge dx_k=0.

The Levi-Civita connection acts on their span through an so(3)-valued
1-form (alpha,beta,gamma). The equations dOmega_i=0 yield a linear
12 by 12 system for its 12 scalar coefficients. In a normalized
orthonormal frame the matrix has determinant 16, so it is invertible:
all three 1-forms vanish. Hence the three Omega_i are parallel.
The metric is hyperkahler, has holonomy contained in SU(2), and is
Ricci-flat. Adding -dt^2 gives Ricci-flat Lorentzian five-dimensional
product geometry. The argument is local and works for every smooth
positive harmonic V, not only affine or radial examples.

**Global obstruction.** A global principal circle bundle with fibre
coordinate psi of period L has normalized circle connection
(2pi/L)Theta. The curvature-integrality condition is

    [F/L] in H^2(U,Z) (under the de Rham/integral comparison).

It must be imposed. For U=R^3 minus one centre and V=c+k/r, the
flux is -4pi*k, so c1=-4pi*k/L. Period L=4pi*k gives c1=-1. For
other positive k and a fixed L there need not be any global circle
bundle; this is not a failure of the local Ricci theorem.

**Lean boundary.** The repository contains the universal first-jet
forms/closure identities and an invertible frame-connection algebra
candidate. It still lacks the smooth tangent-bundle identification,
the construction of the actual Levi-Civita connection on the form
bundle, and the Mathlib hyperkahler=>Ricci theorem. The arbitrary
2-jet metric-to-Ricci step is independently checked by SymPy.

## 2. General cylinder-condition 5D to 4D EMD reduction

Take a 4D Lorentzian metric g, scalar q>0, 1-form A, independent of
psi, and define

    G5=q*g + q^-2(dpsi+A)^2,   q=exp(phi/sqrt(3)).

At any point one can choose Lorentzian normal coordinates for g and
a local circle gauge with A(p)=0. The universal Ricci-jet calculation
has no Einstein equation assumed. Put F=dA, and define residuals

    M^nu = nabla_mu(q^-3 F^mu nu),
    S0 = Box_g(log q) + q^-3 F^2/4,
    E_mu nu = Ric_g(mu,nu) - (3/2)partial_mu(log q)partial_nu(log q)
               -(1/2)q^-3(F_mu rho F_nu^rho - g_mu nu F^2/4).

In a horizontal/vertical frame (with A(p)=0), the independent
second-jet identity is

    Ric5(mu,nu)=E_mu nu - g_mu nu*S0/2,
    Ric5(mu,5)=-g_mu nu*M^nu/2,
    Ric5(5,5)=q^-3*S0.

Tensoriality, together with the invertible fibre-coordinate shear,
restores the formula in an arbitrary A gauge. It follows algebraically
that Ric5=0 iff E=0, M=0 and S0=0. The action identity is

    sqrt(-G5) R5 = sqrt(-g) [R_g -(3/2)|d log q|_g^2
                             -q^-3 F^2/4 - Box_g(log q)].

After integrating the psi circle and discarding an admissible total
boundary divergence, this is Einstein--Maxwell--dilaton with
kinetic term -(1/2)|d phi|^2 and coupling -e^-sqrt(3)phi F^2/4.
The boundary term may only be dropped under suitable boundary and
variation conditions. The sign and normalization match PR #199.

**Lean boundary.** Exact universal normal-gauge second-jet residual
identities are still evaluated by SymPy. Lean proves the algebraic
residual equivalence and the new unrestricted-A 5x5 block inverse,
fibre shift, and tensor shear algebra. It does NOT yet prove arbitrary
smooth metric-to-Ricci differential-geometric identities in Mathlib.

## 3. Global Hopf atlas and single-centre Taub--NUT extension

For V=c+k/r, k>0,c>=0, take psi period L=4pi*k. Set

    rho=2 sqrt(k*r), chi=psi/k (chi modulo 4pi).

The unit S^3 Hopf coordinates are

    z1=rho*cos(theta/2)*exp(i(chi+varphi)/2),
    z2=rho*sin(theta/2)*exp(i(chi-varphi)/2).

The projection (z1,z2)->(2Re(conj z1 z2),2Im(conj z1 z2),
|z1|^2-|z2|^2) has base norm rho^2 and is invariant under common
unit-complex multiplication. Equal base image and radius imply equal
Hermitian rank-one projectors z*z^dagger, hence differ by a unique
phase for rho>0. This identifies the fibres with U(1) orbits.
The two affine base charts on C^2 minus {0} are w_N=z2/z1 and
w_S=z1/z2, and their overlap is w_N*w_S=1. The associated local
unit-circle fibre transition is exp(-i*varphi), with winding -1;
this is precisely c1=-1 and the smooth Hopf S^3 link around rho=0.

For alpha=c/(4k^2)>=0 and X=(Re z1,Im z1,Re z2,Im z2), the spatial
metric equals

    g(X)=Q*delta - alpha*(2+alpha*|X|^2)/Q * omega^2,
    Q=1+alpha*|X|^2,
    omega=X0*dX1-X1*dX0+X2*dX3-X3*dX2.

Every coefficient is C-infinity at X=0; g(0)=delta. The six-square
Lagrange/Cauchy identity gives

    |omega(v)|^2 <= |X|^2 |v|^2,
    g_X(v,v)>=|v|^2/Q>0 for v!=0.

Thus rho=0 adds a smooth R^4 centre with no cone singularity and
radius-rho links exactly S^3, rather than S^3/Z_n. For
integer |n|>1 with L=4pi*k/|n| the link is a lens-space quotient
and the centre is an orbifold, not a smooth manifold point.

**Lean boundary.** The C-infinity metric coefficients and algebraic
Dirac north/south transition are already proved in PR #219. PR #222
proves the global real-polynomial Hopf map, U(1) invariance,
CP^1 affine-chart overlap, and strict metric quadratic positivity.
A genuine Mathlib smooth quotient S^3/U(1), principal-bundle atlas,
transition degree, and global coordinate equivalence still require
formalization; these are the remaining Lean topology obligations.