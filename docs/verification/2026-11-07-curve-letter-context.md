# Curve-letter contextual observation model (2026-11-07)

This is an additive instance of PR #87's quotient criterion, using the curve-letter state in the 2026-10-20 note [クソ玉_定理チェイン到達点.md](https://drive.google.com/file/d/1c3D8UbaAet3hk_gMf0rYZVfSe-xzsSUy/view?usp=drivesdk). It does not change the four-state example or any earlier theorem.

## State and join

The note records a curve-piece signature
\[
S=(z,\alpha,F),\qquad
(z,\alpha,F)\star(w,\beta,G)
=(z+e^{i\alpha}w,\alpha+\beta,F+G).
\]
For its circular-arc example, set \(\xi=2h/(3\pi)\) and \(c_0=\pi^2/(8h)\). Store displacement in units of \(\xi\), angle as the number of quarter turns \(2\alpha/\pi\), and cost in units of \(c_0\). Then
\[
A=(3+3i,1,1),\qquad B=(-1+i,3,9).
\]
A quarter turn acts on \((x,y)\) as \((-y,x)\). The angle coordinate is a lifted count, so four quarter turns remain 4 (angle \(2\pi\)); only the displacement rotation is periodic.

The Lean state is the total integer submodel \((z,\alpha,F)\in\mathbb Z^2\times\mathbb N\times\mathbb N\). Its old action alphabet contains one identity rewrite, and its readout is
\[
O(z,\alpha,F)=(\operatorname{Re}z,\alpha,F).
\]
Thus WordEq under the old action is exactly equality of this readout.

## Exact calculation

Using the join with the left piece's rotation:

| Word | Full normalized state \((z,\alpha,F)\) | Readout \(O\) |
|---|---|---|
| \(AB\) | \((2+2i,4,10)\) | \((2,4,10)\) |
| \(BA\) | \((2-2i,4,10)\) | \((2,4,10)\) |
| \(AAB\) | \((1+5i,5,11)\) | \((1,5,11)\) |
| \(ABA\) | \((5+5i,5,11)\) | \((5,5,11)\) |

The original readout identifies AB and BA; the left context A joined to the hole distinguishes them by endpoint real part 1 versus 5. The full states are noncommutative already at AB ≠ BA.

The Lean additions record the full states and these readout equalities as decidable integer calculations. AB_BA_wordEq and old_quotient_identifies_AB_BA connect the collision to the old predictive quotient. curveJoin_assoc verifies associativity of this discrete operation.

## Connection to PR #87

The instance specializes StableJoin and stable_iff_old_attach_exists from JoinContextualEquivalence.inc:

- StableJoin requires WordEq to be preserved when either argument of the join is replaced by an equivalent state (both left and right attachment).
- The exhibited AB ∼ BA, but A joined to AB is not WordEq to A joined to BA, disproves that condition here.
- Therefore no exact binary attachment agreeing with the join on representatives can be defined on the old WordEq quotient. old_quotient_has_no_exact_attachment proves this by the PR #87 iff theorem.
- The full ContextEq quotient retains the readout and supports attachment through PR #87's readout_encode and attach_encode. It separates the old AB/BA collision.

PR #87's four-state counterexample is a separate finite model: it hides a Boolean bit and uses a custom gated-XOR join, refining two old classes to four. This curve-letter instance instead uses normalized complex displacement, lifted quarter-turn angle, additive cost, and the note's SE(2)-type join. The shared result is the failure of the old observational kernel to be a two-sided join congruence; the states, operation, and class counts are not identified.

## Verification scope and remaining obligations

tests/test_curve_letter_context.py recomputes the exact states with Python tuples and integers, independently of the Lean definitions. The Lean source is registered after PR #87's generic join theorem so the repository's integrated --trust=0 and axiom audit checks the specialization together with the retained declarations.

The encoded A/B signatures are the circular-arc values already derived in the note. The Lean proofs take those normalized signatures as inputs and verify their exact joins and observations; they do not formalize the trigonometric arc integrals or the dimensional normalization from first principles. The source note supplies those analytic values. This patch also does not prove that arbitrary integer tuples are realizable by admissible curves, that a join is smooth at the curvature boundary, or any minimizing-curve, area, or higher-signature claim. The circular concatenation belongs to the note's piecewise-smooth auxiliary model.

