/-!
Word coefficients of noncommutative formal series. Products use only finitely
many cuts of a word; there is no analytic convergence assumption. The actual
iterated integrals satisfy the product and unshuffle-coproduct equations.
This file does not identify all primitive series with a completed free Lie
algebra, and does not assume such an identification.
-/

noncomputable section

namespace LinearInputCurveWordFormalSeries
open LinearInputCurveWordSignature LinearInputCurveWordChen

/-- All word coefficients, with no finite-support restriction. -/
abbrev Series (ι : Type*) := List ι → ℝ

/-- Concatenation product, evaluated by all cuts of the target word. -/
def product {ι : Type*} (F G : Series ι) (w : List ι) : ℝ :=
  ∑ k ∈ Finset.range (w.length + 1), F (w.take k) * G (w.drop k)

def unitSeries {ι : Type*} : Series ι
  | [] => 1
  | _ :: _ => 0

theorem product_empty {ι : Type*} (F G : Series ι) :
    product F G [] = F [] * G [] := by simp [product]

theorem product_cons {ι : Type*} (F G : Series ι) (i : ι) (w : List ι) :
    product F G (i :: w) =
      F [] * G (i :: w) + product (fun z => F (i :: z)) G w := by
  unfold product
  rw [List.length_cons, Finset.sum_range_succ']
  simp only [List.take_zero, List.drop_zero, List.take_succ_cons, List.drop_succ_cons]
  ring

theorem product_add_left {ι : Type*} (F G H : Series ι) :
    product (F + G) H = product F H + product G H := by
  funext w
  simp [product, add_mul, Finset.sum_add_distrib]

theorem product_add_right {ι : Type*} (F G H : Series ι) :
    product F (G + H) = product F G + product F H := by
  funext w
  simp [product, mul_add, Finset.sum_add_distrib]

theorem product_const_left {ι : Type*} (r : ℝ) (F G : Series ι) :
    product (fun w => r * F w) G = fun w => r * product F G w := by
  funext w
  simp [product, Finset.mul_sum, mul_assoc]

theorem product_const_right {ι : Type*} (r : ℝ) (F G : Series ι) :
    product F (fun w => r * G w) = fun w => r * product F G w := by
  funext w
  simp only [product, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem product_zero_left {ι : Type*} (F : Series ι) : product 0 F = 0 := by
  funext w
  simp [product]

theorem product_zero_right {ι : Type*} (F : Series ι) : product F 0 = 0 := by
  funext w
  simp [product]

theorem product_assoc {ι : Type*} (F G H : Series ι) :
    product (product F G) H = product F (product G H) := by
  funext w
  induction w generalizing F G H with
  | nil => simp [product_empty, mul_assoc]
  | cons i w ih =>
    have he : (fun z => product F G (i :: z)) =
        (fun z => F [] * G (i :: z)) + product (fun z => F (i :: z)) G := by
      funext z
      exact product_cons F G i z
    rw [product_cons, product_empty, he, product_add_left, product_const_left]
    simp only [Pi.add_apply]
    rw [ih, product_cons F, product_cons G]
    ring

theorem product_unit_left {ι : Type*} (F : Series ι) :
    product unitSeries F = F := by
  funext w
  cases w with
  | nil => simp [product_empty, unitSeries]
  | cons i w =>
    rw [product_cons]
    change 1 * F (i :: w) + product 0 F w = F (i :: w)
    rw [product_zero_left]
    simp

theorem product_unit_right {ι : Type*} (F : Series ι) :
    product F unitSeries = F := by
  funext w
  induction w generalizing F with
  | nil => simp [product_empty, unitSeries]
  | cons i w ih =>
    rw [product_cons]
    simp only [unitSeries, mul_zero, zero_add]
    exact ih _

/-- Chen's theorem is equality of the entire families of word coefficients. -/
theorem signature_product {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) (a b c : ℝ) :
    signature v a c = product (signature v a b) (signature v b c) := by
  funext w
  exact signature_chen hv a b c w

/-- Coefficients of the unshuffle coproduct; multiplicity is retained. -/
def coproduct {ι : Type*} (F : Series ι) (u w : List ι) : ℝ :=
  ((chronologicalShuffles u w).map F).sum

/-- A coefficient statement of the group-like coproduct equation. -/
def GroupLike {ι : Type*} (F : Series ι) : Prop :=
  F [] = 1 ∧ ∀ u w, coproduct F u w = F u * F w

/-- The primitive coproduct equation, independent of being a log-signature. -/
def Primitive {ι : Type*} (F : Series ι) : Prop :=
  F [] = 0 ∧ ∀ u w, coproduct F u w = F u * unitSeries w + unitSeries u * F w

theorem signature_groupLike {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) (a b : ℝ) :
    GroupLike (signature v a b) := by
  constructor
  · exact signature_empty v a b
  · intro u w
    exact (signature_shuffle hv a b u w).symm

def power {ι : Type*} (F : Series ι) : ℕ → Series ι
  | 0 => unitSeries
  | n + 1 => product F (power F n)

theorem power_zero {ι : Type*} (F : Series ι) : power F 0 = unitSeries := rfl

theorem power_one {ι : Type*} (F : Series ι) : power F 1 = F :=
  product_unit_right F

theorem power_empty {ι : Type*} (F : Series ι) (n : ℕ) :
    power F n [] = (F []) ^ n := by
  induction n with
  | zero => simp [power, unitSeries]
  | succ n ih => simp [power, product_empty, ih, pow_succ, mul_comm]

/-- Positive-order series have no contribution from powers above word length. -/
theorem power_vanishes_above_degree {ι : Type*} {F : Series ι} (hF : F [] = 0)
    (n : ℕ) (w : List ι) (hn : w.length < n) : power F n w = 0 := by
  induction n generalizing w with
  | zero => omega
  | succ n ih =>
    simp only [power, product]
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hk0 : k = 0
    · simp [hk0, hF]
    · have hk' : k ≤ w.length := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hd : (w.drop k).length < n := by
        rw [List.length_drop]
        omega
      rw [ih (w.drop k) hd, mul_zero]

/-- Formal logarithm of a series with constant coefficient one. The formula
is finite coefficientwise; the zero-th term is zero by the scalar factor. -/
def formalLog {ι : Type*} (F : Series ι) (w : List ι) : ℝ :=
  ∑ k ∈ Finset.range (w.length + 1),
    ((-1 : ℝ) ^ (k + 1) / (k : ℝ)) * power (F - unitSeries) k w

/-- Formal exponential of a positive-order series, finite coefficientwise. -/
def formalExp {ι : Type*} (F : Series ι) (w : List ι) : ℝ :=
  ∑ k ∈ Finset.range (w.length + 1),
    (1 / (Nat.factorial k : ℝ)) * power F k w

theorem formalLog_empty {ι : Type*} (F : Series ι) : formalLog F [] = 0 := by
  simp [formalLog]

theorem formalLog_singleton {ι : Type*} (F : Series ι) (i : ι) :
    formalLog F [i] = F [i] := by
  simp [formalLog, Finset.sum_range_succ, power_one, unitSeries]

theorem formalLog_pair {ι : Type*} (F : Series ι) (hF : F [] = 1) (i j : ι) :
    formalLog F [i,j] = F [i,j] - F [i] * F [j] / 2 := by
  simp [formalLog, Finset.sum_range_succ, power, product_cons, product_empty,
    unitSeries, hF]
  ring

theorem formalExp_empty {ι : Type*} (F : Series ι) : formalExp F [] = 1 := by
  simp [formalExp, power, unitSeries]

theorem formalExp_singleton {ι : Type*} (F : Series ι) (i : ι) :
    formalExp F [i] = F [i] := by
  simp [formalExp, Finset.sum_range_succ, power_one, power_zero, unitSeries]

theorem formalExp_pair {ι : Type*} (F : Series ι) (hF : F [] = 0) (i j : ι) :
    formalExp F [i,j] = F [i,j] + F [i] * F [j] / 2 := by
  simp [formalExp, Finset.sum_range_succ, power, product_cons, product_empty,
    unitSeries, hF]
  ring

/-- The antisymmetric degree-two Lie coefficient is derived from the actual
shuffle identity, not posited as a log-signature formula. -/
theorem signature_log_pair {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) (a b : ℝ) (i j : ι) :
    formalLog (signature v a b) [i,j] =
      (signature v a b [i,j] - signature v a b [j,i]) / 2 := by
  rw [formalLog_pair _ (signature_empty v a b)]
  have hs := signature_shuffle hv a b [i] [j]
  simp [chronologicalShuffles, shuffles] at hs
  linarith

/-- The degree-two BCH coefficient for the genuine concatenation product. -/
theorem log_product_pair {ι : Type*} (F G : Series ι)
    (hF : F [] = 1) (hG : G [] = 1) (i j : ι) :
    formalLog (product F G) [i,j] = formalLog F [i,j] + formalLog G [i,j] +
      (F [i] * G [j] - G [i] * F [j]) / 2 := by
  have hFG : product F G [] = 1 := by rw [product_empty, hF, hG, one_mul]
  rw [formalLog_pair _ hFG, formalLog_pair _ hF, formalLog_pair _ hG]
  simp [product_cons, product_empty, hF, hG]
  ring

/-- Every power coefficient depends only on coefficients through that degree. -/
theorem power_congr_through {ι : Type*} {F G : Series ι} (N : ℕ)
    (h : ∀ z, z.length ≤ N → F z = G z) (n : ℕ) (w : List ι)
    (hw : w.length ≤ N) : power F n w = power G n w := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    simp only [power, product]
    apply Finset.sum_congr rfl
    intro k _
    have ht : (w.take k).length ≤ N := by
      simpa only [List.length_take] using le_trans (Nat.min_le_right k w.length) hw
    have hd : (w.drop k).length ≤ N := by
      simpa only [List.length_drop] using le_trans (Nat.sub_le w.length k) hw
    rw [h (w.take k) ht,
      ih (w.drop k) hd]

theorem formalExp_congr_through {ι : Type*} {F G : Series ι} (N : ℕ)
    (h : ∀ z, z.length ≤ N → F z = G z) (w : List ι) (hw : w.length ≤ N) :
    formalExp F w = formalExp G w := by
  unfold formalExp
  apply Finset.sum_congr rfl
  intro n _
  rw [power_congr_through N h n w hw]

/-- Powers at least two only use strictly lower positive-degree coefficients. -/
theorem power_congr_below {ι : Type*} {F G : Series ι}
    (hF : F [] = 0) (hG : G [] = 0) (w : List ι)
    (h : ∀ z, z.length < w.length → F z = G z) (n : ℕ) :
    power F (n + 2) w = power G (n + 2) w := by
  simp only [power, product]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ w.length := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  by_cases h0 : k = 0
  · simp [h0, hF, hG]
  by_cases ht : k = w.length
  · simp [ht, power_empty, hF, hG]
  have hl : (w.take k).length < w.length := by
    rw [List.length_take, Nat.min_eq_left hk']
    omega
  have hr : (w.drop k).length < w.length := by
    rw [List.length_drop]
    omega
  rw [h (w.take k) hl]
  have hp := power_congr_through (w.drop k).length
    (fun z hz => h z (lt_of_le_of_lt hz hr)) (n + 1) (w.drop k) le_rfl
  exact congrArg (fun r => G (w.take k) * r) hp

/-- The exponential is the identity on the current coefficient, plus terms
depending only on strictly lower coefficients. -/
theorem formalExp_difference {ι : Type*} {F G : Series ι}
    (hF : F [] = 0) (hG : G [] = 0) (w : List ι) (hw : w ≠ [])
    (h : ∀ z, z.length < w.length → F z = G z) :
    formalExp F w - formalExp G w = F w - G w := by
  have hlen : 0 < w.length := List.length_pos_iff.mpr hw
  calc
    formalExp F w - formalExp G w =
        ∑ k ∈ Finset.range (w.length + 1),
          (1 / (Nat.factorial k : ℝ)) * (power F k w - power G k w) := by
      simp only [formalExp, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = F w - G w := by
      rw [Finset.sum_eq_single 1]
      · simp [power_one]
      · intro k _ hk1
        by_cases hk0 : k = 0
        · simp [hk0, power]
        · obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
          rw [power_congr_below hF hG w h, sub_self, mul_zero]
      · intro hn
        exact False.elim (hn (Finset.mem_range.mpr (by omega)))

/-- Injectivity is proved by induction on word length, without choosing a log. -/
theorem formalExp_injective {ι : Type*} {F G : Series ι}
    (hF : F [] = 0) (hG : G [] = 0) (he : formalExp F = formalExp G) : F = G := by
  funext w
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases hw : w = []
    · subst w
      exact hF.trans hG.symm
    have hd := formalExp_difference hF hG w hw (fun z hz => ih z.length
      (by omega) z rfl)
    rw [congrFun he w, sub_self] at hd
    linarith

/-- Degree-by-degree construction of the inverse exponential. Each correction
uses the already computed lower degrees. -/
def logApprox {ι : Type*} (F : Series ι) : ℕ → Series ι
  | 0 => 0
  | n + 1 => fun w => if w.length = n + 1 then
      F w - formalExp (logApprox F n) w else logApprox F n w

theorem logApprox_empty {ι : Type*} (F : Series ι) (n : ℕ) :
    logApprox F n [] = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [logApprox] using ih

theorem logApprox_above {ι : Type*} (F : Series ι) (n : ℕ) (w : List ι)
    (hw : n < w.length) : logApprox F n w = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [logApprox, show w.length ≠ n + 1 by omega, if_false]
    exact ih (by omega)

theorem logApprox_stable {ι : Type*} (F : Series ι) (n : ℕ) (w : List ι)
    (hw : w.length ≤ n) : logApprox F (n + 1) w = logApprox F n w := by
  simp only [logApprox, show w.length ≠ n + 1 by omega, if_false]

theorem exp_logApprox {ι : Type*} (F : Series ι) (hF : F [] = 1)
    (n : ℕ) (w : List ι) (hw : w.length ≤ n) : formalExp (logApprox F n) w = F w := by
  induction n generalizing w with
  | zero =>
    have : w = [] := List.length_eq_zero_iff.mp (by omega)
    subst w
    rw [formalExp_empty, hF]
  | succ n ih =>
    by_cases hn : w.length ≤ n
    · rw [formalExp_congr_through n (fun z hz => logApprox_stable F n z hz) w hn]
      exact ih w hn
    · have he : w.length = n + 1 := by omega
      have hw0 : w ≠ [] := by intro hz; simp [hz] at he
      have hd := formalExp_difference (logApprox_empty F (n + 1)) (logApprox_empty F n)
        w hw0 (fun z hz => logApprox_stable F n z (by omega))
      have hs : logApprox F (n + 1) w = F w - formalExp (logApprox F n) w := by
        simp only [logApprox, he, if_true]
      rw [hs, logApprox_above F n w (by omega)] at hd
      linarith

/-- The logarithm is constructed coefficientwise as the unique positive-order
inverse of the explicit exponential; its existence is proved below. -/
def logarithm {ι : Type*} (F : Series ι) (w : List ι) : ℝ :=
  logApprox F w.length w

theorem logApprox_eq_logarithm {ι : Type*} (F : Series ι) (n : ℕ) (w : List ι)
    (hw : w.length ≤ n) : logApprox F n w = logarithm F w := by
  induction n with
  | zero =>
    have he : w.length = 0 := by omega
    simp only [logarithm, he]
  | succ n ih =>
    by_cases hn : w.length ≤ n
    · rw [logApprox_stable F n w hn]
      exact ih hn
    · have he : w.length = n + 1 := by omega
      simp only [logarithm, he]

theorem logarithm_empty {ι : Type*} (F : Series ι) : logarithm F [] = 0 := by
  rw [logarithm, logApprox_empty]

/-- The actual finite-coefficient exponential has a logarithm in every degree. -/
theorem formalExp_logarithm {ι : Type*} (F : Series ι) (hF : F [] = 1) :
    formalExp (logarithm F) = F := by
  funext w
  rw [← formalExp_congr_through w.length
    (fun z hz => logApprox_eq_logarithm F w.length z hz) w le_rfl]
  exact exp_logApprox F hF w.length w le_rfl

theorem logarithm_formalExp {ι : Type*} (F : Series ι) (hF : F [] = 0) :
    logarithm (formalExp F) = F := by
  apply formalExp_injective (logarithm_empty _) hF
  exact formalExp_logarithm _ (formalExp_empty F)

theorem logarithm_singleton {ι : Type*} (F : Series ι) (hF : F [] = 1) (i : ι) :
    logarithm F [i] = F [i] := by
  have h := congrFun (formalExp_logarithm F hF) [i]
  simpa only [formalExp_singleton] using h

theorem logarithm_pair {ι : Type*} (F : Series ι) (hF : F [] = 1) (i j : ι) :
    logarithm F [i,j] = F [i,j] - F [i] * F [j] / 2 := by
  have h := congrFun (formalExp_logarithm F hF) [i,j]
  rw [formalExp_pair _ (logarithm_empty F), logarithm_singleton F hF,
    logarithm_singleton F hF] at h
  linarith

/-- The BCH operation on positive-order associative word series. Its inverse
exponential and associativity laws below hold in every degree. Lie membership
is a separate theorem about the primitive subspace. -/
def bch {ι : Type*} (A B : Series ι) : Series ι :=
  logarithm (product (formalExp A) (formalExp B))

theorem bch_empty {ι : Type*} (A B : Series ι) : bch A B [] = 0 :=
  logarithm_empty _

/-- This is an equality of all coefficients, not a finite-order BCH expansion. -/
theorem formalExp_bch {ι : Type*} (A B : Series ι) :
    formalExp (bch A B) = product (formalExp A) (formalExp B) := by
  apply formalExp_logarithm
  rw [product_empty, formalExp_empty, formalExp_empty, one_mul]

theorem bch_assoc {ι : Type*} (A B C : Series ι) :
    bch (bch A B) C = bch A (bch B C) := by
  apply formalExp_injective (bch_empty _ _) (bch_empty _ _)
  rw [formalExp_bch, formalExp_bch, formalExp_bch, formalExp_bch, product_assoc]

theorem bch_singleton {ι : Type*} (A B : Series ι) (i : ι) :
    bch A B [i] = A [i] + B [i] := by
  have he : product (formalExp A) (formalExp B) [] = 1 := by
    rw [product_empty, formalExp_empty, formalExp_empty, one_mul]
  rw [bch, logarithm_singleton _ he]
  simp [product_cons, product_empty, formalExp_empty, formalExp_singleton, add_comm]

theorem bch_pair {ι : Type*} (A B : Series ι) (hA : A [] = 0) (hB : B [] = 0)
    (i j : ι) : bch A B [i,j] = A [i,j] + B [i,j] +
      (A [i] * B [j] - B [i] * A [j]) / 2 := by
  have he : product (formalExp A) (formalExp B) [] = 1 := by
    rw [product_empty, formalExp_empty, formalExp_empty, one_mul]
  rw [bch, logarithm_pair _ he]
  simp [product_cons, product_empty, formalExp_empty, formalExp_singleton,
    formalExp_pair A hA, formalExp_pair B hB]
  ring

/-- Concatenation of actual signatures is carried to the all-degree BCH operation. -/
theorem signature_logarithm_chen {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) (a b c : ℝ) :
    logarithm (signature v a c) =
      bch (logarithm (signature v a b)) (logarithm (signature v b c)) := by
  unfold bch
  rw [formalExp_logarithm _ (signature_empty v a b),
    formalExp_logarithm _ (signature_empty v b c), ← signature_product hv a b c]

end LinearInputCurveWordFormalSeries
