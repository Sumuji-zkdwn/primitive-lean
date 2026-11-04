import Mathlib

/-!
# General Vieta--Lagrange remainder trace

An arbitrary splitting polynomial with distinct roots is represented by its
nodal product.  `R` is an explicit remainder certificate for `W * Q`.
This is a general field theorem: no numerical roots and no numerical examples.
-/

namespace OrbitTrace

open Polynomial

universe u v

theorem nodal_remainder_trace
    {K : Type u} [Field K] {ι : Type v} [DecidableEq ι]
    (nodes : Finset ι) (roots : ι → K)
    (hinj : Set.InjOn roots (↑nodes : Set ι))
    (W Q R U : Polynomial K)
    (hdeg : R.degree < (nodes.card : WithBot ℕ))
    (hdiv : W * Q = R + Lagrange.nodal nodes roots * U) :
    (∑ i ∈ nodes,
      (eval (roots i) W * eval (roots i) Q) /
        eval (roots i) (derivative (Lagrange.nodal nodes roots))) =
      R.coeff (nodes.card - 1) := by
  calc
    (∑ i ∈ nodes,
        (eval (roots i) W * eval (roots i) Q) /
          eval (roots i) (derivative (Lagrange.nodal nodes roots))) =
        ∑ i ∈ nodes, eval (roots i) R /
          ∏ j ∈ nodes.erase i, (roots i - roots j) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hroot : eval (roots i) (Lagrange.nodal nodes roots) = 0 :=
        Lagrange.eval_nodal_at_node hi
      have heval :
          eval (roots i) W * eval (roots i) Q = eval (roots i) R := by
        have h := congrArg (eval (roots i)) hdiv
        simpa only [eval_mul, eval_add, hroot, zero_mul, add_zero] using h
      rw [heval, Lagrange.eval_nodal_derivative_eval_node_eq hi, Lagrange.eval_nodal]
    _ = R.coeff (nodes.card - 1) :=
      (Lagrange.coeff_eq_sum hinj hdeg).symm

/--
General parametric coefficient-trace theorem.
Here `P - C t * Q` is assumed to have exactly the distinct roots in `nodes`,
and `R` is the certified remainder of `W * Q`.
-/
theorem parametric_remainder_trace
    {K : Type u} [Field K] {ι : Type v} [DecidableEq ι]
    (nodes : Finset ι) (roots : ι → K)
    (hinj : Set.InjOn roots (↑nodes : Set ι))
    (P Q W R U : Polynomial K) (t : K)
    (hfactor : P - C t * Q = Lagrange.nodal nodes roots)
    (hdeg : R.degree < (nodes.card : WithBot ℕ))
    (hdiv : W * Q = R + (P - C t * Q) * U) :
    (∑ i ∈ nodes,
      (eval (roots i) W * eval (roots i) Q) /
        eval (roots i) (derivative (P - C t * Q))) =
      R.coeff (nodes.card - 1) := by
  rw [hfactor] at hdiv ⊢
  exact nodal_remainder_trace nodes roots hinj W Q R U hdeg hdiv

#print axioms OrbitTrace.nodal_remainder_trace
#print axioms OrbitTrace.parametric_remainder_trace

end OrbitTrace
