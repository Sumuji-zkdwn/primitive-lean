import Mathlib

/-!
# Root traces and uniquely determined algebraic moments

For F(X) = X^(p+1) - s*X^p + a with p+1 distinct roots,
Lagrange interpolation gives all initial root moments. The polynomial
relation supplies the same recurrence as canonicalMoment.

All identities are kernel checked, with no root-solving or division
algorithm assumptions; the factorization and distinct roots are explicit.
-/

namespace OrbitTrace

open Polynomial

universe u v

noncomputable def rootPowerSum {K : Type u} [Field K]
    {ι : Type v} [DecidableEq ι]
    (nodes : Finset ι) (roots : ι → K) (k : ℕ) : K :=
  ∑ i ∈ nodes,
    roots i ^ k / eval (roots i) (derivative (Lagrange.nodal nodes roots))

theorem rootPowerSum_initial
    {K : Type u} [Field K] {ι : Type v} [DecidableEq ι]
    (nodes : Finset ι) (roots : ι → K)
    (hinj : Set.InjOn roots (↑nodes : Set ι))
    (p : ℕ) (hcard : nodes.card = p + 1)
    (k : ℕ) (hk : k ≤ p) :
    rootPowerSum nodes roots k = if k = p then 1 else 0 := by
  have hdeg : ((X : Polynomial K) ^ k).degree <
      (nodes.card : WithBot ℕ) := by
    rw [degree_X_pow, hcard]
    norm_cast
    omega
  have hidx : nodes.card - 1 = p := by omega
  calc
    rootPowerSum nodes roots k =
        ∑ i ∈ nodes, eval (roots i) ((X : Polynomial K) ^ k) /
          ∏ j ∈ nodes.erase i, (roots i - roots j) := by
      unfold rootPowerSum
      apply Finset.sum_congr rfl
      intro i hi
      simp only [eval_pow, eval_X,
        Lagrange.eval_nodal_derivative_eval_node_eq hi,
        Lagrange.eval_nodal]
    _ = (((X : Polynomial K) ^ k).coeff (nodes.card - 1)) :=
      (Lagrange.coeff_eq_sum hinj hdeg).symm
    _ = if k = p then 1 else 0 := by
      rw [hidx, coeff_X_pow]
      simp [eq_comm]

theorem root_relation_of_factorization
    {K : Type u} [Field K] {ι : Type v} [DecidableEq ι]
    (nodes : Finset ι) (roots : ι → K)
    (p : ℕ) (s a : K)
    (hfactor : ((X : Polynomial K) ^ (p + 1) -
       C s * X ^ p + C a) = Lagrange.nodal nodes roots)
    (i : ι) (hi : i ∈ nodes) :
    roots i ^ (p + 1) = s * roots i ^ p - a := by
  have heval : eval (roots i)
      ((X : Polynomial K) ^ (p + 1) - C s * X ^ p + C a) = 0 := by
    rw [hfactor]
    exact Lagrange.eval_nodal_at_node hi
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at heval
  linear_combination heval

theorem rootPowerSum_relation
    {K : Type u} [Field K] {ι : Type v} [DecidableEq ι]
    (nodes : Finset ι) (roots : ι → K)
    (p : ℕ) (s a : K)
    (hroot : ∀ i ∈ nodes, roots i ^ (p + 1) = s * roots i ^ p - a)
    (j : ℕ) :
    rootPowerSum nodes roots (j + p + 1) =
      s * rootPowerSum nodes roots (j + p) -
        a * rootPowerSum nodes roots j := by
  unfold rootPowerSum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hr := hroot i hi
  calc
    roots i ^ (j + p + 1) /
        eval (roots i) (derivative (Lagrange.nodal nodes roots)) =
      (roots i ^ j * (s * roots i ^ p - a)) /
        eval (roots i) (derivative (Lagrange.nodal nodes roots)) := by
          rw [show j + p + 1 = j + (p + 1) by omega, pow_add, hr]
    _ = s * (roots i ^ (j + p) /
          eval (roots i) (derivative (Lagrange.nodal nodes roots))) -
        a * (roots i ^ j /
          eval (roots i) (derivative (Lagrange.nodal nodes roots))) := by
          rw [pow_add]
          ring

noncomputable def rootMoment {K : Type u} [Field K]
    {ι : Type v} [DecidableEq ι]
    (nodes : Finset ι) (roots : ι → K) (p k : ℕ) : K :=
  rootPowerSum nodes roots (p + k)

theorem rootMoment_initial
    {K : Type u} [Field K] {ι : Type v} [DecidableEq ι]
    (nodes : Finset ι) (roots : ι → K)
    (hinj : Set.InjOn roots (↑nodes : Set ι))
    (p : ℕ) (hcard : nodes.card = p + 1)
    (s a : K)
    (hroot : ∀ i ∈ nodes, roots i ^ (p + 1) = s * roots i ^ p - a) :
    ∀ k : ℕ, k ≤ p → rootMoment nodes roots p k = s ^ k := by
  intro k
  induction k with
  | zero =>
      intro _
      change rootPowerSum nodes roots p = s ^ 0
      have h := rootPowerSum_initial nodes roots hinj p hcard p (le_refl p)
      simpa using h
  | succ k ih =>
      intro hk
      have hkp : k < p := by omega
      have hz : rootPowerSum nodes roots k = 0 := by
        have h := rootPowerSum_initial nodes roots hinj p hcard k (by omega)
        simpa [Nat.ne_of_lt hkp] using h
      have hr := rootPowerSum_relation nodes roots p s a hroot k
      have h1 : k + p + 1 = p + (k + 1) := by omega
      have h2 : k + p = p + k := by omega
      change rootPowerSum nodes roots (p + (k + 1)) = s ^ (k + 1)
      rw [h1, h2] at hr
      have hprev := ih (by omega)
      change rootPowerSum nodes roots (p + k) = s ^ k at hprev
      rw [hr, hz, hprev]
      ring

theorem rootMoment_recurrence
    {K : Type u} [Field K] {ι : Type v} [DecidableEq ι]
    (nodes : Finset ι) (roots : ι → K)
    (p : ℕ) (s a : K)
    (hroot : ∀ i ∈ nodes, roots i ^ (p + 1) = s * roots i ^ p - a)
    (k : ℕ) :
    rootMoment nodes roots p (k + p + 1) =
      s * rootMoment nodes roots p (k + p) -
        a * rootMoment nodes roots p k := by
  have hr := rootPowerSum_relation nodes roots p s a hroot (p + k)
  have h1 : p + k + p + 1 = p + (k + p + 1) := by omega
  have h2 : p + k + p = p + (k + p) := by omega
  simpa only [rootMoment, h1, h2, Nat.add_assoc] using hr

theorem moment_recurrence_unique
    {K : Type u} [CommRing K] (p : ℕ) (s a : K)
    (M N : ℕ → K)
    (hM0 : ∀ k, k ≤ p → M k = s ^ k)
    (hN0 : ∀ k, k ≤ p → N k = s ^ k)
    (hMr : ∀ k, M (k + p + 1) = s * M (k + p) - a * M k)
    (hNr : ∀ k, N (k + p + 1) = s * N (k + p) - a * N k) :
    M = N := by
  funext k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
      by_cases hk : k ≤ p
      · rw [hM0 k hk, hN0 k hk]
      · have h1 : k - (p + 1) + p + 1 = k := by omega
        have h2 : k - (p + 1) + p = k - 1 := by omega
        have h3 : k - 1 + 1 = k := by omega
        have hl : k - 1 < k := by omega
        have hr : k - (p + 1) < k := by omega
        calc
          M k = s * M (k - 1) - a * M (k - (p + 1)) := by
            simpa only [h1, h2, h3] using hMr (k - (p + 1))
          _ = s * N (k - 1) - a * N (k - (p + 1)) := by
            rw [ih (k - 1) hl, ih (k - (p + 1)) hr]
          _ = N k := by
            simpa only [h1, h2, h3] using (hNr (k - (p + 1))).symm

theorem rootMoment_unique
    {K : Type u} [Field K] {ι : Type v} [DecidableEq ι]
    (nodes : Finset ι) (roots : ι → K)
    (hinj : Set.InjOn roots (↑nodes : Set ι))
    (p : ℕ) (hcard : nodes.card = p + 1)
    (s a : K)
    (hfactor : ((X : Polynomial K) ^ (p + 1) -
       C s * X ^ p + C a) = Lagrange.nodal nodes roots)
    (M : ℕ → K)
    (hinit : ∀ k, k ≤ p → M k = s ^ k)
    (hrec : ∀ k, M (k + p + 1) = s * M (k + p) - a * M k) :
    M = rootMoment nodes roots p := by
  have hroot : ∀ i ∈ nodes,
      roots i ^ (p + 1) = s * roots i ^ p - a := by
    intro i hi
    exact root_relation_of_factorization nodes roots p s a hfactor i hi
  exact moment_recurrence_unique p s a
    M (rootMoment nodes roots p) hinit
    (rootMoment_initial nodes roots hinj p hcard s a hroot)
    hrec (rootMoment_recurrence nodes roots p s a hroot)

#print axioms OrbitTrace.rootPowerSum_initial
#print axioms OrbitTrace.rootMoment_initial
#print axioms OrbitTrace.rootMoment_recurrence
#print axioms OrbitTrace.moment_recurrence_unique
#print axioms OrbitTrace.rootMoment_unique

end OrbitTrace
