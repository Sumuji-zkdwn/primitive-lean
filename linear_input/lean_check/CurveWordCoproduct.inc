/-! The unshuffle coproduct of the coefficient algebra. -/

noncomputable section

namespace LinearInputCurveWordCoproduct
open LinearInputCurveWordSignature LinearInputCurveWordChen
open LinearInputCurveWordFormalSeries

theorem coproduct_nil_left {ι : Type*} (F : Series ι) (w : List ι) :
    coproduct F [] w = F w := by
  simp [coproduct, chronologicalShuffles, shuffles]

theorem coproduct_nil_right {ι : Type*} (F : Series ι) (u : List ι) :
    coproduct F u [] = F u := by
  simp [coproduct, chronologicalShuffles, shuffles_nil_right]

theorem coproduct_snoc_snoc {ι : Type*} (F : Series ι) (u w : List ι) (i j : ι) :
    coproduct F (u ++ [i]) (w ++ [j]) =
      coproduct (fun z => F (z ++ [i])) u (w ++ [j]) +
        coproduct (fun z => F (z ++ [j])) (u ++ [i]) w := by
  simp [coproduct, chronologicalShuffles, List.reverse_append, shuffles,
    List.map_map, Function.comp_def]

theorem coproduct_add {ι : Type*} (F G : Series ι) (u w : List ι) :
    coproduct (F + G) u w = coproduct F u w + coproduct G u w := by
  unfold coproduct
  induction chronologicalShuffles u w with
  | nil => simp
  | cons z zs ih => simp only [List.map_cons, List.sum_cons, Pi.add_apply] at *; linarith

theorem coproduct_const_mul {ι : Type*} (r : ℝ) (F : Series ι) (u w : List ι) :
    coproduct (fun z => r * F z) u w = r * coproduct F u w := by
  unfold coproduct
  induction chronologicalShuffles u w with
  | nil => simp
  | cons z zs ih => simp only [List.map_cons, List.sum_cons] at *; rw [ih]; ring

theorem coproduct_mul_const {ι : Type*} (r : ℝ) (F : Series ι) (u w : List ι) :
    coproduct (fun z => F z * r) u w = coproduct F u w * r := by
  simpa only [mul_comm] using coproduct_const_mul r F u w

theorem product_snoc {ι : Type*} (F G : Series ι) (w : List ι) (i : ι) :
    product F G (w ++ [i]) =
      product F (fun z => G (z ++ [i])) w + F (w ++ [i]) * G [] := by
  simp only [product, List.length_append, List.length_singleton]
  rw [Finset.sum_range_succ]
  have he : ∑ k ∈ Finset.range (w.length + 1),
      F ((w ++ [i]).take k) * G ((w ++ [i]).drop k) =
      ∑ k ∈ Finset.range (w.length + 1), F (w.take k) * G (w.drop k ++ [i]) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ w.length := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [List.take_append_of_le_length hk', List.drop_append_of_le_length hk']
  rw [he]
  rw [List.take_of_length_le (by simp)]
  simp

abbrev BiSeries (ι : Type*) := List ι → List ι → ℝ

def cutSum {ι : Type*} (f : List ι → List ι → ℝ) (w : List ι) : ℝ :=
  ∑ k ∈ Finset.range (w.length + 1), f (w.take k) (w.drop k)

theorem cutSum_add {ι : Type*} (f g : List ι → List ι → ℝ) (w : List ι) :
    cutSum (fun p s => f p s + g p s) w = cutSum f w + cutSum g w := by
  simp [cutSum, Finset.sum_add_distrib]

theorem cutSum_snoc {ι : Type*} (f : List ι → List ι → ℝ) (w : List ι) (i : ι) :
    cutSum f (w ++ [i]) =
      cutSum (fun p s => f p (s ++ [i])) w + f (w ++ [i]) [] := by
  simp only [cutSum, List.length_append, List.length_singleton]
  rw [Finset.sum_range_succ]
  have he : ∑ k ∈ Finset.range (w.length + 1), f ((w ++ [i]).take k) ((w ++ [i]).drop k) =
      ∑ k ∈ Finset.range (w.length + 1), f (w.take k) (w.drop k ++ [i]) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ w.length := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [List.take_append_of_le_length hk', List.drop_append_of_le_length hk']
  rw [he, List.take_of_length_le (by simp)]
  simp

def biProduct {ι : Type*} (P Q : BiSeries ι) (u w : List ι) : ℝ :=
  cutSum (fun p s => cutSum (fun q t => P p q * Q s t) w) u

def tensor {ι : Type*} (F G : Series ι) : BiSeries ι := fun u w => F u * G w

theorem biProduct_tensor {ι : Type*} (F G H K : Series ι) :
    biProduct (tensor F G) (tensor H K) = tensor (product F H) (product G K) := by
  funext u w
  simp only [biProduct, cutSum, tensor, product, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem biProduct_add_right {ι : Type*} (P Q R : BiSeries ι) :
    biProduct P (Q + R) = biProduct P Q + biProduct P R := by
  funext u w
  simp [biProduct, cutSum, mul_add, Finset.sum_add_distrib]

theorem biProduct_snoc_left {ι : Type*} (P Q : BiSeries ι) (u w : List ι) (i : ι) :
    biProduct P Q (u ++ [i]) w =
      biProduct P (fun s t => Q (s ++ [i]) t) u w +
        cutSum (fun q t => P (u ++ [i]) q * Q [] t) w := by
  exact cutSum_snoc (fun p s => cutSum (fun q t => P p q * Q s t) w) u i

theorem biProduct_snoc_right {ι : Type*} (P Q : BiSeries ι) (u w : List ι) (j : ι) :
    biProduct P Q u (w ++ [j]) =
      biProduct P (fun s t => Q s (t ++ [j])) u w +
        cutSum (fun p s => P p (w ++ [j]) * Q s []) u := by
  unfold biProduct
  simp only [cutSum_snoc, cutSum_add]

theorem biProduct_coproduct_snoc_snoc {ι : Type*} (P : BiSeries ι) (G : Series ι)
    (u w : List ι) (i j : ι) :
    biProduct P (coproduct G) (u ++ [i]) (w ++ [j]) =
      biProduct P (coproduct (fun z => G (z ++ [i]))) u (w ++ [j]) +
        biProduct P (coproduct (fun z => G (z ++ [j]))) (u ++ [i]) w +
          P (u ++ [i]) (w ++ [j]) * G [] := by
  have he : (fun s t => coproduct G (s ++ [i]) (t ++ [j])) =
      (fun s t => coproduct (fun z => G (z ++ [i])) s (t ++ [j])) +
        (fun s t => coproduct (fun z => G (z ++ [j])) (s ++ [i]) t) := by
    funext s t
    exact coproduct_snoc_snoc G s t i j
  rw [biProduct_snoc_left, biProduct_snoc_right,
    biProduct_snoc_right P (coproduct (fun z => G (z ++ [i]))),
    biProduct_snoc_left P (coproduct (fun z => G (z ++ [j])))]
  rw [he, biProduct_add_right]
  simp only [Pi.add_apply, cutSum_snoc, coproduct_nil_left, coproduct_nil_right]
  ring

/-- The unshuffle coproduct preserves the full concatenation product. -/
theorem coproduct_product {ι : Type*} (F G : Series ι) (u w : List ι) :
    coproduct (product F G) u w = biProduct (coproduct F) (coproduct G) u w := by
  induction u using List.reverseRecOn generalizing F G w with
  | nil => simp [coproduct_nil_left, biProduct, cutSum, product]
  | append_singleton u i ihu =>
    induction w using List.reverseRecOn generalizing F G with
    | nil => simp [coproduct_nil_right, biProduct, cutSum, product]
    | append_singleton w j ihw =>
      have he (k : ι) : (fun z => product F G (z ++ [k])) =
          product F (fun z => G (z ++ [k])) + (fun z => F (z ++ [k]) * G []) := by
        funext z
        exact product_snoc F G z k
      rw [coproduct_snoc_snoc, he i, he j, coproduct_add, coproduct_add,
        coproduct_mul_const, coproduct_mul_const, ihu, ihw,
        biProduct_coproduct_snoc_snoc, coproduct_snoc_snoc]
      ring

theorem coproduct_zero {ι : Type*} (u w : List ι) : coproduct (0 : Series ι) u w = 0 := by
  change ((chronologicalShuffles u w).map (fun _ => (0 : ℝ))).sum = 0
  simp

theorem coproduct_congr_degree {ι : Type*} {F G : Series ι} (u w : List ι)
    (h : ∀ z, z.length = u.length + w.length → F z = G z) :
    coproduct F u w = coproduct G u w := by
  unfold coproduct
  congr 1
  apply List.map_congr_left
  intro z hz
  exact h z (chronologicalShuffles_word_length u w z hz)

theorem coproduct_unit {ι : Type*} : coproduct (@unitSeries ι) = tensor unitSeries unitSeries := by
  funext u w
  cases u with
  | nil => simp [coproduct_nil_left, tensor, unitSeries]
  | cons i u =>
    cases w with
    | nil => simp [coproduct_nil_right, tensor, unitSeries]
    | cons j w =>
      have he : coproduct unitSeries (i :: u) (j :: w) = coproduct 0 (i :: u) (j :: w) := by
        apply coproduct_congr_degree
        intro z hz
        cases z with
        | nil => simp only [List.length_nil, List.length_cons] at hz; omega
        | cons k z => rfl
      rw [he, coproduct_zero]
      simp [tensor, unitSeries]

theorem coproduct_sum {ι κ : Type*} (s : Finset κ) (F : κ → Series ι) (u w : List ι) :
    coproduct (∑ k ∈ s, F k) u w = ∑ k ∈ s, coproduct (F k) u w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coproduct_zero]
  | @insert k s hk ih => simp only [Finset.sum_insert hk, coproduct_add, ih]

theorem product_sum_right {ι κ : Type*} (F : Series ι) (s : Finset κ) (G : κ → Series ι) :
    product F (∑ k ∈ s, G k) = ∑ k ∈ s, product F (G k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [product_zero_right]
  | @insert k s hk ih => simp only [Finset.sum_insert hk, product_add_right, ih]

theorem biProduct_rows {ι : Type*} (P Q : BiSeries ι) (u : List ι) :
    biProduct P Q u = ∑ k ∈ Finset.range (u.length + 1), product (P (u.take k)) (Q (u.drop k)) := by
  funext w
  simp [biProduct, cutSum, product, Finset.sum_apply]

theorem biProduct_empty_left {ι : Type*} (P Q : BiSeries ι) :
    biProduct P Q [] = product (P []) (Q []) := by
  rw [biProduct_rows]
  simp

theorem biProduct_cons_left {ι : Type*} (P Q : BiSeries ι) (i : ι) (u : List ι) :
    biProduct P Q (i :: u) =
      product (P []) (Q (i :: u)) + biProduct (fun z => P (i :: z)) Q u := by
  simp only [biProduct_rows, List.length_cons, Finset.sum_range_succ', List.take_zero,
    List.drop_zero, List.take_succ_cons, List.drop_succ_cons]
  abel

theorem biProduct_add_left {ι : Type*} (P Q R : BiSeries ι) :
    biProduct (P + Q) R = biProduct P R + biProduct Q R := by
  funext u w
  simp [biProduct, cutSum, add_mul, Finset.sum_add_distrib]

theorem biProduct_coefficient_left {ι : Type*} (R : Series ι) (P Q : BiSeries ι) :
    biProduct (fun u => product R (P u)) Q = fun u => product R (biProduct P Q u) := by
  funext u
  simp only [biProduct_rows, product_assoc, product_sum_right]

theorem biProduct_assoc {ι : Type*} (P Q R : BiSeries ι) :
    biProduct (biProduct P Q) R = biProduct P (biProduct Q R) := by
  funext u
  induction u generalizing P Q R with
  | nil => simp [biProduct_empty_left, product_assoc]
  | cons i u ih =>
    have he : (fun z => biProduct P Q (i :: z)) =
        (fun z => product (P []) (Q (i :: z))) + biProduct (fun z => P (i :: z)) Q := by
      funext z
      exact biProduct_cons_left P Q i z
    rw [biProduct_cons_left, biProduct_empty_left, he, biProduct_add_left,
      biProduct_coefficient_left]
    simp only [Pi.add_apply]
    rw [ih, biProduct_cons_left P, biProduct_cons_left Q, product_add_right, product_assoc]
    abel

theorem biProduct_unit_left {ι : Type*} (P : BiSeries ι) :
    biProduct (tensor unitSeries unitSeries) P = P := by
  funext u w
  have he : biProduct (tensor unitSeries unitSeries) P u w =
      product unitSeries (fun s => product unitSeries (P s) w) u := by
    simp only [biProduct, cutSum, tensor, product, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he]
  simp only [product_unit_left]

theorem biProduct_unit_right {ι : Type*} (P : BiSeries ι) :
    biProduct P (tensor unitSeries unitSeries) = P := by
  funext u w
  have he : biProduct P (tensor unitSeries unitSeries) u w =
      product (fun p => product (P p) unitSeries w) unitSeries u := by
    simp only [biProduct, cutSum, tensor, product, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he]
  simp only [product_unit_right]

theorem biProduct_zero_left {ι : Type*} (P : BiSeries ι) : biProduct 0 P = 0 := by
  funext u w
  simp [biProduct, cutSum]

theorem biProduct_zero_right {ι : Type*} (P : BiSeries ι) : biProduct P 0 = 0 := by
  funext u w
  simp [biProduct, cutSum]

theorem biProduct_const_left {ι : Type*} (r : ℝ) (P Q : BiSeries ι) :
    biProduct (fun u w => r * P u w) Q = fun u w => r * biProduct P Q u w := by
  funext u w
  simp [biProduct, cutSum, Finset.mul_sum, mul_assoc]

theorem biProduct_const_right {ι : Type*} (r : ℝ) (P Q : BiSeries ι) :
    biProduct P (fun u w => r * Q u w) = fun u w => r * biProduct P Q u w := by
  funext u w
  simp only [biProduct, cutSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- A distinct type for the tensor-product coefficient multiplication. -/
def BiTensorSeries (ι : Type*) := BiSeries ι

instance {ι : Type*} : AddCommGroup (BiTensorSeries ι) :=
  inferInstanceAs (AddCommGroup (BiSeries ι))

instance {ι : Type*} : Module ℝ (BiTensorSeries ι) :=
  inferInstanceAs (Module ℝ (BiSeries ι))

instance {ι : Type*} : Ring (BiTensorSeries ι) where
  __ := (inferInstance : AddCommGroup (BiTensorSeries ι))
  mul := biProduct
  one := tensor unitSeries unitSeries
  mul_assoc := biProduct_assoc
  one_mul := biProduct_unit_left
  mul_one := biProduct_unit_right
  left_distrib := biProduct_add_right
  right_distrib := biProduct_add_left
  zero_mul := biProduct_zero_left
  mul_zero := biProduct_zero_right

instance {ι : Type*} : Algebra ℝ (BiTensorSeries ι) :=
  Algebra.ofModule (fun r P Q => biProduct_const_left r P Q)
    (fun r P Q => biProduct_const_right r P Q)

def biPower {ι : Type*} (P : BiSeries ι) : ℕ → BiSeries ι
  | 0 => tensor unitSeries unitSeries
  | n + 1 => biProduct P (biPower P n)

theorem biPower_eq_pow {ι : Type*} (P : BiTensorSeries ι) (n : ℕ) :
    biPower P n = (P ^ n : BiTensorSeries ι) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change biProduct P (biPower P n) = _
    rw [ih, pow_succ']
    rfl

def biExp {ι : Type*} (P : BiSeries ι) (u w : List ι) : ℝ :=
  ∑ n ∈ Finset.range (u.length + w.length + 1),
    (1 / (Nat.factorial n : ℝ)) * biPower P n u w

theorem coproduct_power {ι : Type*} (F : Series ι) (n : ℕ) :
    coproduct (power F n) = biPower (coproduct F) n := by
  induction n with
  | zero => exact coproduct_unit
  | succ n ih =>
    funext u w
    simp only [power, biPower, coproduct_product, ih]

theorem coproduct_formalExp {ι : Type*} (F : Series ι) :
    coproduct (formalExp F) = biExp (coproduct F) := by
  funext u w
  have he : coproduct (formalExp F) u w =
      coproduct (∑ n ∈ Finset.range (u.length + w.length + 1),
        fun z => (1 / (Nat.factorial n : ℝ)) * power F n z) u w := by
    apply coproduct_congr_degree
    intro z hz
    simp only [formalExp, hz, Finset.sum_apply]
  rw [he, coproduct_sum]
  simp only [coproduct_const_mul, coproduct_power, biExp]

theorem biPower_one {ι : Type*} (P : BiSeries ι) : biPower P 1 = P :=
  biProduct_unit_right P

theorem biPower_empty {ι : Type*} (P : BiSeries ι) (n : ℕ) :
    biPower P n [] [] = (P [] []) ^ n := by
  induction n with
  | zero => simp [biPower, tensor, unitSeries]
  | succ n ih => simp [biPower, biProduct, cutSum, ih, pow_succ, mul_comm]

theorem biPower_congr_through {ι : Type*} {P Q : BiSeries ι} (N : ℕ)
    (h : ∀ s t, s.length + t.length ≤ N → P s t = Q s t) (n : ℕ)
    (u w : List ι) (hw : u.length + w.length ≤ N) : biPower P n u w = biPower Q n u w := by
  induction n generalizing u w with
  | zero => rfl
  | succ n ih =>
    change biProduct P (biPower P n) u w = biProduct Q (biPower Q n) u w
    unfold biProduct cutSum
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    dsimp only
    have ht : (u.take k).length + (w.take l).length ≤ N := by
      simp only [List.length_take]
      omega
    have hd : (u.drop k).length + (w.drop l).length ≤ N := by
      simp only [List.length_drop]
      omega
    rw [h _ _ ht, ih _ _ hd]

theorem biPower_congr_below {ι : Type*} {P Q : BiSeries ι}
    (hP : P [] [] = 0) (hQ : Q [] [] = 0) (u w : List ι)
    (h : ∀ s t, s.length + t.length < u.length + w.length → P s t = Q s t) (n : ℕ) :
    biPower P (n + 2) u w = biPower Q (n + 2) u w := by
  change biProduct P (biPower P (n + 1)) u w = biProduct Q (biPower Q (n + 1)) u w
  unfold biProduct cutSum
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  dsimp only
  have hk' : k ≤ u.length := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hl' : l ≤ w.length := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
  by_cases h0 : k + l = 0
  · have hk0 : k = 0 := by omega
    have hl0 : l = 0 := by omega
    simp [hk0, hl0, hP, hQ]
  by_cases he : k + l = u.length + w.length
  · have hk1 : k = u.length := by omega
    have hl1 : l = w.length := by omega
    simp [hk1, hl1, biPower_empty, hP, hQ]
  have ht : (u.take k).length + (w.take l).length < u.length + w.length := by
    simp only [List.length_take, Nat.min_eq_left hk', Nat.min_eq_left hl']
    omega
  have hd : (u.drop k).length + (w.drop l).length < u.length + w.length := by
    simp only [List.length_drop]
    omega
  rw [h _ _ ht]
  have hp := biPower_congr_through ((u.drop k).length + (w.drop l).length)
    (fun s t hst => h s t (lt_of_le_of_lt hst hd)) (n + 1) (u.drop k) (w.drop l) le_rfl
  rw [hp]

theorem biExp_difference {ι : Type*} {P Q : BiSeries ι}
    (hP : P [] [] = 0) (hQ : Q [] [] = 0) (u w : List ι)
    (hw : 0 < u.length + w.length)
    (h : ∀ s t, s.length + t.length < u.length + w.length → P s t = Q s t) :
    biExp P u w - biExp Q u w = P u w - Q u w := by
  calc
    biExp P u w - biExp Q u w =
        ∑ n ∈ Finset.range (u.length + w.length + 1),
          (1 / (Nat.factorial n : ℝ)) * (biPower P n u w - biPower Q n u w) := by
      simp only [biExp, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = P u w - Q u w := by
      rw [Finset.sum_eq_single 1]
      · simp [biPower_one]
      · intro n _ hn1
        by_cases hn0 : n = 0
        · simp [hn0, biPower]
        · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
          rw [biPower_congr_below hP hQ u w h, sub_self, mul_zero]
      · intro hn
        exact False.elim (hn (Finset.mem_range.mpr (by omega)))

theorem biExp_injective {ι : Type*} {P Q : BiSeries ι}
    (hP : P [] [] = 0) (hQ : Q [] [] = 0) (he : biExp P = biExp Q) : P = Q := by
  funext u w
  induction hn : u.length + w.length using Nat.strong_induction_on generalizing u w with
  | ind n ih =>
    by_cases hw : u.length + w.length = 0
    · have hu : u = [] := List.length_eq_zero_iff.mp (by omega)
      have hw' : w = [] := List.length_eq_zero_iff.mp (by omega)
      subst u
      subst w
      exact hP.trans hQ.symm
    have hd := biExp_difference hP hQ u w (by omega)
      (fun s t hst => ih (s.length + t.length) (by omega) s t rfl)
    rw [congrFun (congrFun he u) w, sub_self] at hd
    linarith

theorem power_unit {ι : Type*} (n : ℕ) : power (@unitSeries ι) n = unitSeries := by
  induction n with
  | zero => rfl
  | succ n ih => rw [power, ih, product_unit_left]

theorem biPower_tensor {ι : Type*} (A B : Series ι) (n : ℕ) :
    biPower (tensor A B) n = tensor (power A n) (power B n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [biPower, ih, biProduct_tensor]; rfl

theorem tensor_left_right_commute {ι : Type*} (A B : Series ι) :
    @Commute (BiTensorSeries ι) (inferInstance : Mul (BiTensorSeries ι))
      (tensor A unitSeries) (tensor unitSeries B) := by
  change biProduct (tensor A unitSeries) (tensor unitSeries B) =
    biProduct (tensor unitSeries B) (tensor A unitSeries)
  rw [biProduct_tensor, biProduct_tensor, product_unit_right, product_unit_left,
    product_unit_left, product_unit_right]

theorem biTensor_sum_apply {ι κ : Type*} (s : Finset κ) (P : κ → BiTensorSeries ι)
    (u w : List ι) : (∑ k ∈ s, P k) u w = ∑ k ∈ s, P k u w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rfl
  | @insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    change P k u w + (∑ k ∈ s, P k) u w = P k u w + ∑ k ∈ s, P k u w
    rw [ih]

theorem biTensor_nsmul_apply {ι : Type*} (n : ℕ) (P : BiTensorSeries ι) (u w : List ι) :
    (n • P) u w = n • P u w := by
  induction n with
  | zero => simp only [zero_smul]; rfl
  | succ n ih =>
    rw [succ_nsmul]
    change (n • P) u w + P u w = (n + 1) • P u w
    rw [ih, succ_nsmul]

theorem biPower_tensor_sum {ι : Type*} (A B : Series ι) (n : ℕ) (u w : List ι) :
    biPower (tensor A unitSeries + tensor unitSeries B) n u w =
      ∑ p ∈ Finset.antidiagonal n,
        (n.choose p.1 : ℝ) * (power A p.1 u * power B p.2 w) := by
  let L : BiTensorSeries ι := tensor A unitSeries
  let R : BiTensorSeries ι := tensor unitSeries B
  have hcomm : Commute L R := tensor_left_right_commute A B
  have hb := hcomm.add_pow' n
  have he := congrArg (fun P : BiTensorSeries ι => P u w) hb
  rw [← biPower_eq_pow] at he
  trans ((∑ m ∈ Finset.antidiagonal n, n.choose m.1 • (L ^ m.1 * R ^ m.2)) : BiTensorSeries ι) u w
  · exact he
  rw [biTensor_sum_apply]
  simp_rw [biTensor_nsmul_apply]
  apply Finset.sum_congr rfl
  intro p _
  rw [← biPower_eq_pow, ← biPower_eq_pow]
  dsimp only [L, R]
  rw [biPower_tensor, biPower_tensor,
    power_unit, power_unit]
  change (n.choose p.1) •
    biProduct (tensor (power A p.1) unitSeries) (tensor unitSeries (power B p.2)) u w = _
  rw [biProduct_tensor, product_unit_right, product_unit_left]
  simp only [tensor, nsmul_eq_mul]

theorem exp_binomial_term {ι : Type*} (A B : Series ι) (n : ℕ) (u w : List ι) :
    (1 / (Nat.factorial n : ℝ)) *
        biPower (tensor A unitSeries + tensor unitSeries B) n u w =
      ∑ p ∈ Finset.antidiagonal n,
        ((1 / (Nat.factorial p.1 : ℝ)) * power A p.1 u) *
          ((1 / (Nat.factorial p.2 : ℝ)) * power B p.2 w) := by
  rw [biPower_tensor_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
  have hkn : p.1 ≤ n := by omega
  have hsub : n - p.1 = p.2 := by omega
  have hc : (n.choose p.1 : ℝ) * (Nat.factorial p.1 : ℝ) *
      (Nat.factorial p.2 : ℝ) = (Nat.factorial n : ℝ) := by
    exact_mod_cast (by simpa only [hsub] using Nat.choose_mul_factorial_mul_factorial hkn)
  have hn0 : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hi0 : (Nat.factorial p.1 : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p.1
  have hj0 : (Nat.factorial p.2 : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p.2
  have hcoeff : (1 / (Nat.factorial n : ℝ)) * (n.choose p.1 : ℝ) =
      (1 / (Nat.factorial p.1 : ℝ)) * (1 / (Nat.factorial p.2 : ℝ)) := by
    field_simp
    nlinarith [hc]
  calc
    _ = ((1 / (Nat.factorial n : ℝ)) * (n.choose p.1 : ℝ)) *
        (power A p.1 u * power B p.2 w) := by ring
    _ = _ := by rw [hcoeff]; ring

/-- Exponentials of the commuting left and right tensor factors factorize.
The infinite-sum lemma is used only on finitely supported coefficient sequences. -/
theorem biExp_tensor_sum {ι : Type*} (A B : Series ι) (hA : A [] = 0) (hB : B [] = 0) :
    biExp (tensor A unitSeries + tensor unitSeries B) = tensor (formalExp A) (formalExp B) := by
  funext u w
  let f : ℕ → ℝ := fun n => (1 / (Nat.factorial n : ℝ)) * power A n u
  let g : ℕ → ℝ := fun n => (1 / (Nat.factorial n : ℝ)) * power B n w
  have hf : ∀ n ∉ Finset.range (u.length + 1), f n = 0 := by
    intro n hn
    dsimp only [f]
    rw [power_vanishes_above_degree hA n u (by simp only [Finset.mem_range] at hn; omega), mul_zero]
  have hg : ∀ n ∉ Finset.range (w.length + 1), g n = 0 := by
    intro n hn
    dsimp only [g]
    rw [power_vanishes_above_degree hB n w (by simp only [Finset.mem_range] at hn; omega), mul_zero]
  have hfn : Summable (fun n => ‖f n‖) := summable_of_ne_finset_zero
    (s := Finset.range (u.length + 1)) (fun n hn => by rw [hf n hn, norm_zero])
  have hgn : Summable (fun n => ‖g n‖) := summable_of_ne_finset_zero
    (s := Finset.range (w.length + 1)) (fun n hn => by rw [hg n hn, norm_zero])
  have hfg : ∀ n ∉ Finset.range (u.length + w.length + 1),
      (∑ p ∈ Finset.antidiagonal n, f p.1 * g p.2) = 0 := by
    intro n hn
    apply Finset.sum_eq_zero
    intro p hp
    have hp' : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
    by_cases hi : p.1 ∈ Finset.range (u.length + 1)
    · have hj : p.2 ∉ Finset.range (w.length + 1) := by
        simp only [Finset.mem_range] at *
        omega
      rw [hg p.2 hj, mul_zero]
    · rw [hf p.1 hi, zero_mul]
  calc
    biExp (tensor A unitSeries + tensor unitSeries B) u w =
        ∑ n ∈ Finset.range (u.length + w.length + 1),
          ∑ p ∈ Finset.antidiagonal n, f p.1 * g p.2 := by
      unfold biExp
      apply Finset.sum_congr rfl
      intro n _
      exact exp_binomial_term A B n u w
    _ = ∑' n, ∑ p ∈ Finset.antidiagonal n, f p.1 * g p.2 := (tsum_eq_sum hfg).symm
    _ = (∑' n, f n) * (∑' n, g n) :=
      (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn).symm
    _ = tensor (formalExp A) (formalExp B) u w := by
      rw [tsum_eq_sum hf, tsum_eq_sum hg]
      rfl

/-- A group-like full coefficient series has a primitive logarithm. -/
theorem logarithm_primitive {ι : Type*} {F : Series ι} (hF : GroupLike F) :
    Primitive (logarithm F) := by
  refine ⟨logarithm_empty F, ?_⟩
  have he : biExp (coproduct (logarithm F)) =
      biExp (tensor (logarithm F) unitSeries + tensor unitSeries (logarithm F)) := by
    rw [← coproduct_formalExp, formalExp_logarithm F hF.1,
      biExp_tensor_sum _ _ (logarithm_empty F) (logarithm_empty F),
      formalExp_logarithm F hF.1]
    funext u w
    exact hF.2 u w
  have hp : coproduct (logarithm F) [] [] = 0 := by
    rw [coproduct_nil_left, logarithm_empty]
  have hq : (tensor (logarithm F) unitSeries + tensor unitSeries (logarithm F)) [] [] = 0 := by
    simp [tensor, logarithm_empty, unitSeries]
  have hh := biExp_injective hp hq he
  intro u w
  exact congrFun (congrFun hh u) w

theorem signature_logarithm_primitive {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) (a b : ℝ) : Primitive (logarithm (signature v a b)) :=
  logarithm_primitive (signature_groupLike hv a b)

theorem formalExp_groupLike_of_primitive {ι : Type*} {A : Series ι} (hA : Primitive A) :
    GroupLike (formalExp A) := by
  refine ⟨formalExp_empty A, ?_⟩
  have he : coproduct A = tensor A unitSeries + tensor unitSeries A := by
    funext u w
    exact hA.2 u w
  have hh := coproduct_formalExp A
  rw [he, biExp_tensor_sum A A hA.1 hA.1] at hh
  intro u w
  exact congrFun (congrFun hh u) w

theorem groupLike_product {ι : Type*} {F G : Series ι} (hF : GroupLike F) (hG : GroupLike G) :
    GroupLike (product F G) := by
  constructor
  · rw [LinearInputCurveWordFormalSeries.product_empty, hF.1, hG.1, one_mul]
  · have heF : coproduct F = tensor F F := by funext u w; exact hF.2 u w
    have heG : coproduct G = tensor G G := by funext u w; exact hG.2 u w
    intro u w
    rw [coproduct_product, heF, heG, biProduct_tensor]
    rfl

/-- The all-degree BCH operation preserves the primitive coefficient space. -/
theorem bch_primitive {ι : Type*} {A B : Series ι} (hA : Primitive A) (hB : Primitive B) :
    Primitive (bch A B) :=
  logarithm_primitive (groupLike_product
    (formalExp_groupLike_of_primitive hA) (formalExp_groupLike_of_primitive hB))

end LinearInputCurveWordCoproduct
