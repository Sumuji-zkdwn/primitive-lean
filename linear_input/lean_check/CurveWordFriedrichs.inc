/-! The Dynkin operator and the free-Lie realization of primitive coefficients. -/

noncomputable section

namespace LinearInputCurveWordFriedrichs
open LinearInputCurveWordFormalSeries LinearInputCurveWordCoproduct

/-- The coefficient formula for the convolution `S * Y`, where `S` is reversal
with sign and `Y` multiplies a word by its degree. -/
def dynkin {ι : Type*} (F : Series ι) (w : List ι) : ℝ :=
  ∑ k ∈ Finset.range (w.length + 1),
    (-1 : ℝ) ^ k * (w.length - k : ℕ) *
      coproduct F (w.take k).reverse (w.drop k)

theorem dynkin_empty {ι : Type*} (F : Series ι) : dynkin F [] = 0 := by
  simp [dynkin]

theorem unitSeries_eq_zero_of_ne_nil {ι : Type*} (w : List ι) (hw : w ≠ []) :
    unitSeries w = 0 := by cases w <;> simp_all [unitSeries]

/-- The Dynkin operator multiplies the degree-n part of any primitive series
by n. This statement does not assume a Lie-polynomial representation. -/
theorem dynkin_primitive {ι : Type*} {F : Series ι} (hF : Primitive F) (w : List ι) :
    dynkin F w = (w.length : ℝ) * F w := by
  cases w with
  | nil => simp [dynkin_empty]
  | cons i w =>
    unfold dynkin
    rw [Finset.sum_eq_single 0]
    · simp [hF.2, unitSeries]
    · intro k hk hk0
      have hk' : k ≤ (i :: w).length := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      by_cases he : k = (i :: w).length
      · simp [he]
      · have ht : (List.take k (i :: w)).reverse ≠ [] := by
          intro h
          have hh := congrArg List.length h
          simp only [List.length_reverse, List.length_take, List.length_nil] at hh
          omega
        have hd : List.drop k (i :: w) ≠ [] := by
          intro h
          have hh := congrArg List.length h
          simp only [List.length_drop, List.length_nil] at hh
          omega
        rw [hF.2, unitSeries_eq_zero_of_ne_nil _ ht, unitSeries_eq_zero_of_ne_nil _ hd]
        ring
    · simp

theorem dynkin_add {ι : Type*} (F G : Series ι) :
    dynkin (F + G) = dynkin F + dynkin G := by
  funext w
  simp [dynkin, coproduct_add, mul_add, Finset.sum_add_distrib]

theorem dynkin_const_mul {ι : Type*} (r : ℝ) (F : Series ι) :
    dynkin (fun w => r * F w) = fun w => r * dynkin F w := by
  funext w
  simp only [dynkin, coproduct_const_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- A separate type prevents confusion with the pointwise ring on functions. -/
def TensorSeries (ι : Type*) := Series ι

instance {ι : Type*} : AddCommGroup (TensorSeries ι) :=
  inferInstanceAs (AddCommGroup (Series ι))

instance {ι : Type*} : Module ℝ (TensorSeries ι) :=
  inferInstanceAs (Module ℝ (Series ι))

instance {ι : Type*} : Ring (TensorSeries ι) where
  __ := (inferInstance : AddCommGroup (TensorSeries ι))
  mul := product
  one := unitSeries
  mul_assoc := product_assoc
  one_mul := product_unit_left
  mul_one := product_unit_right
  left_distrib := product_add_right
  right_distrib := product_add_left
  zero_mul := product_zero_left
  mul_zero := product_zero_right

instance {ι : Type*} : Algebra ℝ (TensorSeries ι) :=
  Algebra.ofModule (fun r F G => product_const_left r F G)
    (fun r F G => product_const_right r F G)

/-- The coefficient of a single noncommutative word. -/
def delta {ι : Type*} [DecidableEq ι] (w : List ι) : TensorSeries ι :=
  fun z => if z = w then 1 else 0

/-- The universal map from the actual free Lie algebra into the completed
tensor algebra, sending a generator to its singleton-word coefficient. -/
def lieExpansion {ι : Type*} [DecidableEq ι] :
    FreeLieAlgebra ℝ ι →ₗ⁅ℝ⁆ TensorSeries ι :=
  FreeLieAlgebra.lift ℝ (fun i => delta [i])

def rcons {ι : Type*} [DecidableEq ι] (F : Series ι) (a : ι) (w : List ι) : ℝ :=
  match w.reverse with
  | [] => 0
  | i :: z => if i = a then F z.reverse else 0

def lcons {ι : Type*} [DecidableEq ι] (F : Series ι) (a : ι) : Series ι
  | [] => 0
  | i :: z => if i = a then F z else 0

theorem rcons_nil {ι : Type*} [DecidableEq ι] (F : Series ι) (a : ι) :
    rcons F a [] = 0 := rfl

theorem rcons_snoc {ι : Type*} [DecidableEq ι] (F : Series ι) (a i : ι) (w : List ι) :
    rcons F a (w ++ [i]) = if i = a then F w else 0 := by simp [rcons]

theorem coproduct_zero {ι : Type*} (u w : List ι) : coproduct (0 : Series ι) u w = 0 := by
  unfold coproduct
  change ((LinearInputCurveWordChen.chronologicalShuffles u w).map (fun _ => (0 : ℝ))).sum = 0
  simp

theorem coproduct_zero_fun {ι : Type*} (u w : List ι) :
    coproduct (fun _ : List ι => (0 : ℝ)) u w = 0 := by
  simp [coproduct]

theorem coproduct_rcons {ι : Type*} [DecidableEq ι] (F : Series ι) (a : ι) (u w : List ι) :
    coproduct (rcons F a) u w =
      rcons (fun z => coproduct F z w) a u + rcons (fun z => coproduct F u z) a w := by
  induction u using List.reverseRecOn with
  | nil => simp [coproduct_nil_left, rcons_nil]
  | append_singleton u i _ =>
    induction w using List.reverseRecOn with
    | nil => simp [coproduct_nil_right, rcons_nil]
    | append_singleton w j _ =>
      rw [coproduct_snoc_snoc, rcons_snoc, rcons_snoc]
      by_cases hi : i = a <;> by_cases hj : j = a <;>
        simp only [rcons_snoc, hi, hj, if_true, if_false, coproduct_zero_fun, add_zero, zero_add]

/-- The convolution `S * id`, used to expose the cancellation in Dynkin's formula. -/
def antipodeConvolution {ι : Type*} (F : Series ι) (w : List ι) : ℝ :=
  ∑ k ∈ Finset.range (w.length + 1),
    (-1 : ℝ) ^ k * coproduct F (w.take k).reverse (w.drop k)

theorem antipodeConvolution_empty {ι : Type*} (F : Series ι) :
    antipodeConvolution F [] = F [] := by simp [antipodeConvolution, coproduct_nil_left]

theorem dynkin_rcons_left {ι : Type*} [DecidableEq ι] (F : Series ι) (a : ι) (w : List ι) :
    (∑ k ∈ Finset.range (w.length + 1), (-1 : ℝ) ^ k * (w.length - k : ℕ) *
      rcons (fun z => coproduct F z (w.drop k)) a (w.take k).reverse) =
      -lcons (dynkin F) a w := by
  cases w with
  | nil => simp [rcons_nil, lcons]
  | cons i w =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.take_zero, List.reverse_nil, rcons_nil, mul_zero, add_zero,
      List.take_succ_cons, List.reverse_cons, List.drop_succ_cons, rcons_snoc,
      Nat.add_sub_add_right, pow_succ, lcons]
    by_cases hi : i = a
    · simp only [hi, if_true, dynkin, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    · simp [hi]

theorem dynkin_rcons_right {ι : Type*} [DecidableEq ι] (F : Series ι) (a : ι) (w : List ι) :
    (∑ k ∈ Finset.range (w.length + 1), (-1 : ℝ) ^ k * (w.length - k : ℕ) *
      rcons (fun z => coproduct F (w.take k).reverse z) a (w.drop k)) =
      rcons (dynkin F + antipodeConvolution F) a w := by
  induction w using List.reverseRecOn with
  | nil => simp [rcons_nil]
  | append_singleton w i _ =>
    rw [List.length_append, List.length_singleton, Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, mul_zero, zero_mul, add_zero]
    rw [rcons_snoc]
    by_cases hi : i = a
    · simp only [hi, if_true, Pi.add_apply, dynkin, antipodeConvolution, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ w.length := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [List.take_append_of_le_length hk', List.drop_append_of_le_length hk', rcons_snoc]
      simp only [if_true]
      have hn : w.length + 1 - k = w.length - k + 1 := by omega
      rw [hn, Nat.cast_add, Nat.cast_one]
      ring
    · simp only [hi, if_false]
      apply Finset.sum_eq_zero
      intro k hk
      have hk' : k ≤ w.length := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [List.drop_append_of_le_length hk', rcons_snoc]
      simp [hi]

theorem dynkin_rcons {ι : Type*} [DecidableEq ι] (F : Series ι) (a : ι) :
    dynkin (rcons F a) = rcons (dynkin F + antipodeConvolution F) a - lcons (dynkin F) a := by
  funext w
  simp only [dynkin, coproduct_rcons, mul_add, Finset.sum_add_distrib]
  rw [dynkin_rcons_left, dynkin_rcons_right]
  simp only [Pi.sub_apply]
  ring

theorem antipode_rcons_left {ι : Type*} [DecidableEq ι] (F : Series ι) (a : ι) (w : List ι) :
    (∑ k ∈ Finset.range (w.length + 1), (-1 : ℝ) ^ k *
      rcons (fun z => coproduct F z (w.drop k)) a (w.take k).reverse) =
      -lcons (antipodeConvolution F) a w := by
  cases w with
  | nil => simp [rcons_nil, lcons]
  | cons i w =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.take_zero, List.reverse_nil, rcons_nil, mul_zero, add_zero,
      List.take_succ_cons, List.reverse_cons, List.drop_succ_cons, rcons_snoc, pow_succ, lcons]
    by_cases hi : i = a
    · simp only [hi, if_true, antipodeConvolution, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    · simp [hi]

theorem antipode_rcons_right {ι : Type*} [DecidableEq ι] (F : Series ι) (a : ι) (w : List ι) :
    (∑ k ∈ Finset.range (w.length + 1), (-1 : ℝ) ^ k *
      rcons (fun z => coproduct F (w.take k).reverse z) a (w.drop k)) =
      rcons (antipodeConvolution F) a w := by
  induction w using List.reverseRecOn with
  | nil => simp [rcons_nil]
  | append_singleton w i _ =>
    rw [List.length_append, List.length_singleton, Finset.sum_range_succ]
    have hd : List.drop (w.length + 1) (w ++ [i]) = [] := by simp
    rw [hd, rcons_nil, mul_zero, add_zero, rcons_snoc]
    by_cases hi : i = a
    · simp only [hi, if_true, antipodeConvolution]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ w.length := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [List.take_append_of_le_length hk', List.drop_append_of_le_length hk', rcons_snoc]
      simp only [if_true]
    · simp only [hi, if_false]
      apply Finset.sum_eq_zero
      intro k hk
      have hk' : k ≤ w.length := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [List.drop_append_of_le_length hk', rcons_snoc]
      simp [hi]

theorem antipode_rcons {ι : Type*} [DecidableEq ι] (F : Series ι) (a : ι) :
    antipodeConvolution (rcons F a) =
      rcons (antipodeConvolution F) a - lcons (antipodeConvolution F) a := by
  funext w
  simp only [antipodeConvolution, coproduct_rcons, mul_add, Finset.sum_add_distrib]
  rw [antipode_rcons_left, antipode_rcons_right]
  simp only [Pi.sub_apply]
  ring

theorem rcons_delta {ι : Type*} [DecidableEq ι] (u : List ι) (a : ι) :
    rcons (delta u) a = delta (u ++ [a]) := by
  funext w
  induction w using List.reverseRecOn with
  | nil => simp [rcons_nil, delta]
  | append_singleton w i _ =>
    rw [rcons_snoc]
    simp only [delta]
    by_cases hi : i = a <;> by_cases hw : w = u <;> simp_all

theorem delta_nil {ι : Type*} [DecidableEq ι] : delta ([] : List ι) = unitSeries := by
  funext w
  cases w <;> simp [delta, unitSeries]

theorem coproduct_unit {ι : Type*} (u w : List ι) :
    coproduct unitSeries u w = unitSeries u * unitSeries w := by
  induction u using List.reverseRecOn with
  | nil => simp [coproduct_nil_left, unitSeries]
  | append_singleton u i _ =>
    induction w using List.reverseRecOn with
    | nil => simp [coproduct_nil_right, unitSeries]
    | append_singleton w j _ =>
      rw [coproduct_snoc_snoc]
      have hu (z : List ι) (k : ι) : unitSeries (z ++ [k]) = 0 := by
        cases z <;> rfl
      simp only [hu, coproduct_zero_fun, zero_add, mul_zero]

theorem dynkin_unit {ι : Type*} : dynkin (@unitSeries ι) = 0 := by
  funext w
  cases w with
  | nil => exact dynkin_empty _
  | cons i w =>
    unfold dynkin
    apply Finset.sum_eq_zero
    intro k hk
    rw [coproduct_unit]
    cases k with
    | zero => simp [unitSeries]
    | succ k =>
      have hz : (List.take (k + 1) (i :: w)).reverse ≠ [] := by simp
      rw [unitSeries_eq_zero_of_ne_nil _ hz]
      ring

theorem antipode_unit {ι : Type*} : antipodeConvolution (@unitSeries ι) = unitSeries := by
  funext w
  cases w with
  | nil => simp [antipodeConvolution_empty]
  | cons i w =>
    change _ = 0
    unfold antipodeConvolution
    apply Finset.sum_eq_zero
    intro k hk
    rw [coproduct_unit]
    cases k with
    | zero => simp [unitSeries]
    | succ k =>
      have hz : (List.take (k + 1) (i :: w)).reverse ≠ [] := by simp
      rw [unitSeries_eq_zero_of_ne_nil _ hz]
      ring

theorem antipode_delta {ι : Type*} [DecidableEq ι] (u : List ι) (hu : u ≠ []) :
    antipodeConvolution (delta u) = 0 := by
  induction u using List.reverseRecOn with
  | nil => contradiction
  | append_singleton u i ih =>
    rw [← rcons_delta, antipode_rcons]
    by_cases he : u = []
    · subst u
      rw [delta_nil, antipode_unit]
      funext w
      cases w with
      | nil => simp [rcons_nil, lcons]
      | cons j w =>
        change rcons unitSeries i (j :: w) - lcons unitSeries i (j :: w) = 0
        induction w using List.reverseRecOn with
        | nil => simp [rcons, lcons, unitSeries]
        | append_singleton w k _ =>
          rw [show j :: (w ++ [k]) = (j :: w) ++ [k] from rfl, rcons_snoc]
          cases w <;> simp [unitSeries, lcons]
    · rw [ih he]
      funext w
      induction w using List.reverseRecOn with
      | nil => simp [rcons_nil, lcons]
      | append_singleton w j _ =>
        change rcons 0 i (w ++ [j]) - lcons 0 i (w ++ [j]) = 0
        rw [rcons_snoc]
        cases w <;> simp [lcons]

theorem rcons_zero {ι : Type*} [DecidableEq ι] (a : ι) : rcons (0 : Series ι) a = 0 := by
  funext w
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w i _ => simp [rcons_snoc]

theorem lcons_zero {ι : Type*} [DecidableEq ι] (a : ι) : lcons (0 : Series ι) a = 0 := by
  funext w
  cases w <;> simp [lcons]

theorem rcons_unit {ι : Type*} [DecidableEq ι] (a : ι) : rcons unitSeries a = delta [a] := by
  simpa [delta_nil] using rcons_delta ([] : List ι) a

theorem dynkin_singleton {ι : Type*} [DecidableEq ι] (a : ι) : dynkin (delta [a]) = delta [a] := by
  rw [← rcons_unit, dynkin_rcons, dynkin_unit, antipode_unit, zero_add,
    lcons_zero, sub_zero, rcons_unit]

theorem product_delta_right {ι : Type*} [DecidableEq ι] (F : Series ι) (a : ι) :
    product F (delta [a]) = rcons F a := by
  funext w
  induction w using List.reverseRecOn with
  | nil => simp [LinearInputCurveWordFormalSeries.product_empty, delta, rcons_nil]
  | append_singleton w i _ =>
    rw [product_snoc, rcons_snoc]
    have he : (fun z => delta [a] (z ++ [i])) =
        (if i = a then unitSeries else 0 : Series ι) := by
      funext z
      cases z <;> by_cases hi : i = a <;> simp [delta, unitSeries, hi]
    rw [he]
    have hz : delta [a] [] = 0 := by simp [delta]
    rw [hz, mul_zero, add_zero]
    by_cases hi : i = a <;> simp [hi, product_unit_right, product_zero_right]

theorem product_delta_left {ι : Type*} [DecidableEq ι] (F : Series ι) (a : ι) :
    product (delta [a]) F = lcons F a := by
  funext w
  cases w with
  | nil => simp [LinearInputCurveWordFormalSeries.product_empty, delta, lcons]
  | cons i w =>
    rw [product_cons]
    have he : (fun z => delta [a] (i :: z)) =
        (if i = a then unitSeries else 0 : Series ι) := by
      funext z
      cases z <;> by_cases hi : i = a <;> simp [delta, unitSeries, hi]
    rw [he]
    have hz : delta [a] [] = 0 := by simp [delta]
    rw [hz, zero_mul, zero_add]
    by_cases hi : i = a <;> simp [hi, product_unit_left, product_zero_left, lcons]

/-- The left-nested bracket of a nonempty word, as an element of Mathlib's
free Lie algebra. The empty word is sent to zero. -/
def nestedLie {ι : Type*} : List ι → FreeLieAlgebra ℝ ι
  | [] => 0
  | a :: w => w.foldl (fun x b => ⁅x, FreeLieAlgebra.of ℝ b⁆) (FreeLieAlgebra.of ℝ a)

theorem nestedLie_snoc {ι : Type*} (u : List ι) (a : ι) (hu : u ≠ []) :
    nestedLie (u ++ [a]) = ⁅nestedLie u, FreeLieAlgebra.of ℝ a⁆ := by
  cases u with
  | nil => contradiction
  | cons i u => simp [nestedLie, List.foldl_append]

/-- Dynkin's word identity: the convolution operator sends each tensor word
to its actual left-nested free-Lie bracket under the universal expansion. -/
theorem dynkin_delta_eq_lieExpansion {ι : Type*} [DecidableEq ι] (u : List ι) :
    dynkin (delta u) = lieExpansion (nestedLie u) := by
  induction u using List.reverseRecOn with
  | nil =>
    rw [delta_nil, dynkin_unit]
    change (0 : TensorSeries ι) = lieExpansion 0
    exact (map_zero lieExpansion).symm
  | append_singleton u a ih =>
    by_cases hu : u = []
    · subst u
      simp [nestedLie, dynkin_singleton, lieExpansion, FreeLieAlgebra.lift_of_apply]
    · rw [nestedLie_snoc u a hu, LieHom.map_lie, Ring.lie_def]
      have hg : lieExpansion (FreeLieAlgebra.of ℝ a) = delta [a] := by
        simp [lieExpansion]
      rw [hg, ← rcons_delta, dynkin_rcons, antipode_delta u hu, add_zero]
      change rcons (dynkin (delta u)) a - lcons (dynkin (delta u)) a =
        product (lieExpansion (nestedLie u)) (delta [a]) -
          product (delta [a]) (lieExpansion (nestedLie u))
      rw [product_delta_left, product_delta_right, ih]

def homogeneous {ι : Type*} (F : Series ι) (n : ℕ) (w : List ι) : ℝ :=
  if w.length = n then F w else 0

theorem coproduct_homogeneous {ι : Type*} (F : Series ι) (n : ℕ) (u w : List ι) :
    coproduct (homogeneous F n) u w =
      if u.length + w.length = n then coproduct F u w else 0 := by
  have hm : (LinearInputCurveWordChen.chronologicalShuffles u w).map (homogeneous F n) =
      (LinearInputCurveWordChen.chronologicalShuffles u w).map
        (fun z => if u.length + w.length = n then F z else 0) := by
    apply List.map_congr_left
    intro z hz
    simp only [homogeneous, LinearInputCurveWordChen.chronologicalShuffles_word_length u w z hz]
  unfold coproduct
  rw [hm]
  split <;> simp_all

theorem primitive_homogeneous {ι : Type*} {F : Series ι} (hF : Primitive F) (n : ℕ) :
    Primitive (homogeneous F n) := by
  constructor
  · simp [homogeneous, hF.1]
  · intro u w
    cases u with
    | nil => simp [coproduct_nil_left, homogeneous, hF.1, unitSeries]
    | cons i u =>
      cases w with
      | nil => simp [coproduct_nil_right, homogeneous, hF.1, unitSeries]
      | cons j w => simp [coproduct_homogeneous, hF.2, unitSeries]

def degreeWords (ι : Type*) [Fintype ι] [DecidableEq ι] (n : ℕ) : Finset (List ι) :=
  Finset.univ.image (List.ofFn : (Fin n → ι) → List ι)

theorem mem_degreeWords {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) (w : List ι) :
    w ∈ degreeWords ι n ↔ w.length = n := by
  constructor
  · intro h
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp h
    simp
  · intro h
    subst n
    exact Finset.mem_image.mpr ⟨w.get, Finset.mem_univ _, List.ofFn_get w⟩

theorem homogeneous_delta_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Series ι) (n : ℕ) :
    homogeneous F n = ∑ u ∈ degreeWords ι n, (fun w => F u * delta u w) := by
  funext w
  simp [homogeneous, Finset.sum_apply, delta, mul_ite, mem_degreeWords]

theorem dynkin_zero {ι : Type*} : dynkin (0 : Series ι) = 0 := by
  funext w
  simp [dynkin, coproduct_zero]

theorem dynkin_sum {ι κ : Type*} (s : Finset κ) (F : κ → Series ι) :
    dynkin (∑ k ∈ s, F k) = ∑ k ∈ s, dynkin (F k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dynkin_zero]
  | @insert k s hk ih => simp [Finset.sum_insert, hk, dynkin_add, ih]

/-- A concrete degree-n free-Lie element constructed from all length-n words.
Finiteness of the alphabet makes this an algebraic finite sum. -/
def primitiveLieDegree {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Series ι) (n : ℕ) : FreeLieAlgebra ℝ ι :=
  (n : ℝ)⁻¹ • ∑ u ∈ degreeWords ι n, F u • nestedLie u

/-- The homogeneous Friedrichs theorem, with an explicit free-Lie witness. -/
theorem primitiveLieDegree_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : Series ι} (hF : Primitive F) (n : ℕ) (hn : n ≠ 0) :
    lieExpansion (primitiveLieDegree F n) = homogeneous F n := by
  have hd : dynkin (homogeneous F n) = fun w => (n : ℝ) * homogeneous F n w := by
    funext w
    rw [dynkin_primitive (primitive_homogeneous hF n)]
    by_cases hw : w.length = n
    · rw [hw]
    · simp [homogeneous, hw]
  have he : lieExpansion (∑ u ∈ degreeWords ι n, F u • nestedLie u) =
      dynkin (homogeneous F n) := by
    rw [homogeneous_delta_sum F n, dynkin_sum]
    simp only [map_sum, map_smul, dynkin_const_mul, dynkin_delta_eq_lieExpansion]
    rfl
  unfold primitiveLieDegree
  rw [map_smul, he, hd]
  funext w
  change (n : ℝ)⁻¹ * ((n : ℝ) * homogeneous F n w) = homogeneous F n w
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [← mul_assoc, inv_mul_cancel₀ hn', one_mul]

/-- Every primitive coefficient series over a finite alphabet is the
degreewise expansion of actual elements of the free Lie algebra. -/
theorem primitive_has_freeLie_degrees {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : Series ι} (hF : Primitive F) :
    ∃ L : ℕ → FreeLieAlgebra ℝ ι, L 0 = 0 ∧
      ∀ n, lieExpansion (L n) = homogeneous F n := by
  refine ⟨primitiveLieDegree F, ?_, ?_⟩
  · simp [primitiveLieDegree]
  · intro n
    by_cases hn : n = 0
    · subst n
      have hzero : homogeneous F 0 = 0 := by
        funext w
        cases w <;> simp [homogeneous, hF.1]
      rw [hzero]
      have hz : primitiveLieDegree F 0 = 0 := by simp [primitiveLieDegree]
      rw [hz, map_zero]
      rfl
    · exact primitiveLieDegree_expansion hF n hn

/-- The span of length-n nested generator brackets inside the actual free Lie
algebra. This records the homogeneity of the constructed witnesses. -/
def lieDegree (ι : Type*) (n : ℕ) : Submodule ℝ (FreeLieAlgebra ℝ ι) :=
  Submodule.span ℝ {x | ∃ w : List ι, w.length = n ∧ nestedLie w = x}

theorem primitiveLieDegree_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Series ι) (n : ℕ) : primitiveLieDegree F n ∈ lieDegree ι n := by
  unfold primitiveLieDegree
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro u hu
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨u, (mem_degreeWords n u).mp hu, rfl⟩

/-- A finite-alphabet primitive series has an explicitly homogeneous sequence
of free-Lie elements whose coefficient expansions recover the entire series. -/
theorem primitive_completed_lie_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : Series ι} (hF : Primitive F) :
    ∃ L : ℕ → FreeLieAlgebra ℝ ι, L 0 = 0 ∧
      (∀ n, L n ∈ lieDegree ι n) ∧
      ∀ n w, lieExpansion (L n) w = if w.length = n then F w else 0 := by
  refine ⟨primitiveLieDegree F, ?_, primitiveLieDegree_mem F, ?_⟩
  · simp [primitiveLieDegree]
  · intro n w
    by_cases hn : n = 0
    · subst n
      have hz : primitiveLieDegree F 0 = 0 := by simp [primitiveLieDegree]
      rw [hz, map_zero]
      cases w <;> simp [hF.1] <;> rfl
    · rw [primitiveLieDegree_expansion hF n hn]
      rfl

/-- The logarithm of the signature defined by actual iterated integrals lies
degree by degree in the image of the actual free Lie algebra. -/
theorem signature_logarithm_completed_lie {ι : Type*} [Fintype ι] [DecidableEq ι]
    {v : ι → ℝ → ℝ} (hv : ∀ i, Continuous (v i)) (a b : ℝ) :
    ∃ L : ℕ → FreeLieAlgebra ℝ ι, L 0 = 0 ∧
      (∀ n, L n ∈ lieDegree ι n) ∧
      ∀ n w, lieExpansion (L n) w =
        if w.length = n then logarithm (LinearInputCurveWordSignature.signature v a b) w else 0 :=
  primitive_completed_lie_expansion (signature_logarithm_primitive hv a b)

/-- The BCH series of primitive inputs also has actual homogeneous free-Lie
witnesses at every degree. -/
theorem bch_completed_lie {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Series ι} (hA : Primitive A) (hB : Primitive B) :
    ∃ L : ℕ → FreeLieAlgebra ℝ ι, L 0 = 0 ∧
      (∀ n, L n ∈ lieDegree ι n) ∧
      ∀ n w, lieExpansion (L n) w = if w.length = n then bch A B w else 0 :=
  primitive_completed_lie_expansion (bch_primitive hA hB)

end LinearInputCurveWordFriedrichs
