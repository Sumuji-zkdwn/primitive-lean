# Gravity-only U(1) monopole in a non-product Ricci-flat 5D metric

2026-11-22 (JST). Exact local tensor calculation passed independently; dedicated Lean kernel CI pending.

## Core result

Unlike the positive-Lambda Einstein products in draft PR #180, this model uses **Lambda=0** and no independent Maxwell field. Consider the Gross–Perry–Sorkin / Gibbons–Hawking geometry

    ds5²=-dt²+H(r)[dr²+r²(dtheta²+sin²theta dphi²)]
          +H(r)^(-1)[dpsi+k*cos(theta)dphi]²,
    H(r)=1+k/r.

For all r>0, the radial harmonic equation and the Gibbons–Hawking connection condition are

    d/dr[r² H'(r)]=0,
    d[k*cos(theta)dphi]=[*_3 dH]=-k*sin(theta)dtheta^dphi.

The exact independent SymPy checker constructs the full 4x4 spatial metric, forms its inverse and Christoffels, then proves by symbolic simplification that every one of the 10 independent Ricci tensor components is zero for k=1. Adding a time factor -dt² gives a 5D Lorentzian Ricci-flat metric. The general k analytic harmonic identity is also checked.

The additional circle's connection has nonzero magnetic curvature in the lower-dimensional observer description, although the five-dimensional theory is pure vacuum Einstein gravity. The circle radius varies with r: this is NOT a fixed-radius Cartesian product and the reduced 4D fields include a dilaton.

## Topology and physical interpretation

Use north and south gauge potentials A_N=k(cos(theta)-1)dphi and A_S=k(cos(theta)+1)dphi. Their difference is 2k dphi. With psi periodic of 4pi*k (k>0), the transition around phi ∈ [0,2pi] winds once. The normalized circle angle chi=psi/(2k) has period 2pi, and its connection F=-sin(theta)/2 dtheta^dphi yields int(S²)F/(2pi)=-1. The magnetic flux has a genuine topological invariant; it cannot be removed by a globally smooth circle-coordinate change.

Full smoothness at r=0 and global extension rely on standard Taub–NUT geometry. The independent checker establishes **local Ricci flatness on r>0** and exact Chern-number arithmetic, not a Lean proof of the smooth atlas.

## Lean/Python provenance and bounds

- lean/Research/KKMonopoleGeometry.lean: algebraic constant radial flux, patch transition, orientation reversal and normalised Chern arithmetic. This does not directly check differential geometry in Lean.
- tools/check_kk_monopole.py: all 10 spatial Ricci tensor components, harmonicity for general k, first Chern number from symbolic integration.
- .github/workflows/kk-monopole.yml: pinned exact-head Lean compilation, axioms, independent SymPy oracle.

This advances gravity-only reconstruction for an Abelian magnetic monopole but does NOT reconstruct observed particles, electric charge spectra, non-Abelian gauge dynamics, chiral matter, or quantum theory. It is an established 1983 family of solutions, not a new physical discovery.

## References

- Gross–Perry–Sorkin monopole in 5D vacuum gravity: https://doi.org/10.1103/PhysRevD.72.044007
- Higher-dimensional Taub–NUT vacuum solutions: https://doi.org/10.1016/j.nuclphysb.2005.09.019
- Gibbons–Hawking local form and harmonic potential: https://www.collectionscanada.gc.ca/obj/thesescanada/vol2/SSU/TC-SSU-201112249.pdf
