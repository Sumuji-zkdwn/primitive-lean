# Pair-interaction cocycles and Newton specialization (2026-11-03)

## Relationship to the original chain

The source on this branch extends the algebraic model of curved-path
composition discussed in `HistorySignature.inc` and the 2026-10-20
"クソ玉定理チェイン" research note. The former has a *signed area* cross
term (a skew 2-cocycle associated to the SE(2) action). This proof introduces
a **new symmetric pair potential** on finite disjoint sets of labelled
particles.

For an arbitrary kernel W(i,j), define
C_W(A,B) = sum(i in A, j in B) W(i,j).
For pairwise-disjoint A, B, C, the cocycle identity is
C(A,B)+C(A∪B,C)=C(B,C)+C(A,B∪C).

If W is symmetric, define U_W(A)= [C_W(A,A)-sum(i in A)W(i,i)]/2.
Then for disjoint A, B,
C_W(A,B)=U_W(A∪B)-U_W(A)-U_W(B).
Thus the gravity cocycle is **exact/a coboundary**, unlike the specific
noncommutative area geometry. Associativity alone does not choose W.

Choose W_G(i,j)=-G*m_i*m_j / dist(x_i,x_j) for distinct labels.
For positive separation x<y on the line,
F_x = -d/dx[-G*m1*m2/(y-x)] = +G*m1*m2/(y-x)^2.

## Explicit limitations

1. General metric space here only supplies distances to the pair potential;
   it does not imply the Newton field law, spatial geometry, or an equation
   of motion.
2. Collisions and coincident positions are excluded from the physical model,
   even though the Lean definition uses field division where 1/0=0.
3. This does NOT prove a full 3D gradient theorem, inverse-square uniqueness
   from Gauss law, Einstein equations, material viscosity, or nontrivial
   equivalence between the gravity and area cocycles.
4. Each component is an additive proof target, not an assertion of a new
   general physical law. Source provenance and strict Lean audit must pass
   before marking these theorems verified.
