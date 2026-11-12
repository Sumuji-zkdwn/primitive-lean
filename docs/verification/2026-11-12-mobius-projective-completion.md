# WFS Möbius map on the extended complex line (2026-11-12)

## Pin and provenance

Base: main commit 28721702d21720c37805fb64924253f3e1ace11f.

The original WFS real-domain calculations are retained, unchanged:
- linear_input/lean_check/WFSMobiusFourier.inc
- linear_input/lean_check/WFSProjectiveSampling.inc

The group-action and three-point LFT proofs are an attributed upstream
dependency, NOT original results from primitive-lean.

- Fubin Yan and Kenneth Shum, "Formalizing Extended Complex Numbers,
  Möbius Transformations, and Cross Ratio in Lean 4" (2026),
  https://arxiv.org/abs/2606.20358
- https://github.com/fubinyan/ComplexVariables
- source: MAT3253/Chapter02/EComplex.lean at commit
  bfdb91564bb5aafe0c3e7ec73501e43598146b13
- copied unchanged to lean/Research/EComplexThirdParty.lean
- license: Apache-2.0; preserved in licenses/Mobius-Apache-2.0.txt
- source checked with THIS repository's pinned Lean 4.30.0-rc2 in PR CI.

## New Lean claims

lean/Research/MobiusProjectiveCompletion.lean proves:
1. The specific matrix [[-1,0],[2,1]] has nonzero determinant and
   squares to the identity.
2. Its induced action on EComplex = Option Complex is an involution
   including the infinity point.
3. Its pole -1/2 and infinity are exchanged exactly.
4. Every invertible complex 2x2 matrix scales the alternating bracket
   of two homogeneous pairs by its determinant.
5. The resulting homogeneous cross ratio is invariant under ALL such
   matrices, with a deliberately totalized complex-division convention.
6. Distinguished homogeneous representatives for finite points and infinity.
7. The existing upstream general three-point existence and functional
   uniqueness theorems are exposed as bridge lemmas.
8. Functionally equal invertible matrices are exactly those with
   proportional coefficients (upstream theorem), the algebraic
   identification used for a projective group quotient.

The homogeneous cross ratio is on coordinate pairs; the theorem does
not yet identify it with a separately constructed quotient type
PGL(2,C), or prove topological/conformal/circline classification.
The WFS bridge is an equality of indicated projective actions,
not a derivation of the original physical WFS response law.

Important: none here is a valid new real-number result 1/0 = infinity.
The map is total only because its state space is changed to Option Complex.

## Verification

The PR's dedicated workflow compiles the unchanged upstream file and
the extension with --trust=0, checks for admitted placeholders,
and prints axiom dependencies for selected general and new theorems.
A completed success run at the exact PR head is needed before calling
the integrated results Lean-verified on the pinned project toolchain.
