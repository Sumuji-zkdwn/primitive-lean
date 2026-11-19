/-!
All-degree Chen identities for the actual iterated interval integrals.
The velocity is continuous in every coordinate. All endpoints are arbitrary
real numbers; oriented interval integration supplies the direction conventions.
-/

noncomputable section

namespace LinearInputCurveWordChen
open Real MeasureTheory
open LinearInputCurveWordSignature

theorem reverseIntegral_split {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) (a b c : ℝ) (w : List ι) :
    reverseIntegral v a w c =
      ∑ k ∈ Finset.range (w.length + 1),
        reverseIntegral v b (w.take k) c * reverseIntegral v a (w.drop k) b := by
  induction w generalizing c with
  | nil => simp [reverseIntegral]
  | cons i w ih =>
    have hc := (reverseIntegral_continuous hv a w).mul (hv i)
    have hs := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hc.intervalIntegrable a b) (hc.intervalIntegrable b c)
    simp only [Pi.mul_apply] at hs
    have he : (fun t => reverseIntegral v a w t * v i t) =
        fun t => ∑ k ∈ Finset.range (w.length + 1),
          (reverseIntegral v b (w.take k) t * v i t) *
            reverseIntegral v a (w.drop k) b := by
      funext t
      rw [ih, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hint : ∀ k ∈ Finset.range (w.length + 1),
        IntervalIntegrable (fun t =>
          (reverseIntegral v b (w.take k) t * v i t) *
            reverseIntegral v a (w.drop k) b) volume b c := by
      intro k _
      exact (((reverseIntegral_continuous hv b (w.take k)).mul (hv i)).mul
        continuous_const).intervalIntegrable b c
    have hrest : (∫ t in b..c, reverseIntegral v a w t * v i t) =
        ∑ k ∈ Finset.range (w.length + 1),
          reverseIntegral v b (i :: w.take k) c *
            reverseIntegral v a (w.drop k) b := by
      rw [he, intervalIntegral.integral_finsetSum hint]
      apply Finset.sum_congr rfl
      intro k _
      rw [intervalIntegral.integral_mul_const]
      rfl
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.take_succ_cons, List.drop_succ_cons, List.take_zero,
      List.drop_zero, reverseIntegral, one_mul]
    simp only [reverseIntegral] at hrest
    rw [← hs, hrest]
    ring

/-- Chen's identity at every finite degree, in chronological word order. -/
theorem signature_chen {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) (a b c : ℝ) (w : List ι) :
    signature v a c w =
      ∑ k ∈ Finset.range (w.length + 1),
        signature v a b (w.take k) * signature v b c (w.drop k) := by
  rw [signature, reverseIntegral_split hv a b c w.reverse]
  simp only [List.length_reverse]
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ w.length := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  simp only [Nat.add_sub_cancel, List.take_reverse, List.drop_reverse,
    Nat.sub_sub_self hk', signature]
  ring

/-- Interleavings retain multiplicity: equal letters do not remove repeated words. -/
def shuffles {ι : Type*} : List ι → List ι → List (List ι)
  | [], v => [v]
  | u, [] => [u]
  | i :: u, j :: v =>
      ((shuffles u (j :: v)).map (i :: ·)) ++
        ((shuffles (i :: u) v).map (j :: ·))
termination_by u v => u.length + v.length

theorem shuffles_nil_right {ι : Type*} (u : List ι) : shuffles u [] = [u] := by
  cases u <;> simp [shuffles]

theorem continuous_list_sum {κ : Type*} (l : List κ) (f : κ → ℝ → ℝ)
    (hf : ∀ k, Continuous (f k)) :
    Continuous (fun t => (l.map (fun k => f k t)).sum) := by
  induction l with
  | nil => simpa using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
  | cons k l ih =>
    convert (hf k).add ih using 1
    rfl

theorem integral_list_sum {κ : Type*} (l : List κ) (f : κ → ℝ → ℝ)
    (hf : ∀ k, Continuous (f k)) (a b : ℝ) :
    (∫ t in a..b, (l.map (fun k => f k t)).sum) =
      (l.map (fun k => ∫ t in a..b, f k t)).sum := by
  induction l with
  | nil => simp
  | cons k l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [intervalIntegral.integral_add ((hf k).intervalIntegrable a b)
      ((continuous_list_sum l f hf).intervalIntegrable a b), ih]

theorem reverseIntegral_hasDerivAt {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) (a t : ℝ) (i : ι) (w : List ι) :
    HasDerivAt (reverseIntegral v a (i :: w))
      (reverseIntegral v a w t * v i t) t := by
  exact (((reverseIntegral_continuous hv a w).mul (hv i)).integral_hasStrictDerivAt a t).hasDerivAt

theorem sum_reverseIntegral_cons {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) (a b : ℝ) (i : ι) (ws : List (List ι)) :
    (ws.map (fun w => reverseIntegral v a (i :: w) b)).sum =
      ∫ t in a..b, (ws.map (fun w => reverseIntegral v a w t)).sum * v i t := by
  have he : (fun t => (ws.map (fun w => reverseIntegral v a w t)).sum * v i t) =
      fun t => (ws.map (fun w => reverseIntegral v a w t * v i t)).sum := by
    funext t
    induction ws with
    | nil => simp
    | cons w ws ih =>
      simpa only [List.map_cons, List.sum_cons, add_mul] using
        congrArg (fun z => reverseIntegral v a w t * v i t + z) ih
  rw [he, integral_list_sum ws (fun w t => reverseIntegral v a w t * v i t)
    (fun w => (reverseIntegral_continuous hv a w).mul (hv i))]
  rfl

/-- The shuffle formula follows from integration by parts, in every degree. -/
theorem reverseIntegral_shuffle {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) (a b : ℝ) (u w : List ι) :
    reverseIntegral v a u b * reverseIntegral v a w b =
      ((shuffles u w).map (fun z => reverseIntegral v a z b)).sum := by
  cases u with
  | nil => simp [shuffles, reverseIntegral]
  | cons i u =>
    cases w with
    | nil => simp [shuffles_nil_right, reverseIntegral]
    | cons j w =>
      have hp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (fun t _ => reverseIntegral_hasDerivAt hv a t i u)
        (fun t _ => reverseIntegral_hasDerivAt hv a t j w)
        (((reverseIntegral_continuous hv a u).mul (hv i)).intervalIntegrable a b)
        (((reverseIntegral_continuous hv a w).mul (hv j)).intervalIntegrable a b)
      have hz1 : reverseIntegral v a (i :: u) a = 0 := by simp [reverseIntegral]
      have hz2 : reverseIntegral v a (j :: w) a = 0 := by simp [reverseIntegral]
      rw [hz1, hz2, zero_mul, sub_zero] at hp
      rw [shuffles, List.map_append, List.sum_append]
      simp only [List.map_map, Function.comp_def]
      rw [sum_reverseIntegral_cons hv, sum_reverseIntegral_cons hv]
      have h1 : (fun t =>
          ((shuffles u (j :: w)).map (fun z => reverseIntegral v a z t)).sum * v i t) =
          fun t => (reverseIntegral v a u t * v i t) *
            reverseIntegral v a (j :: w) t := by
        funext t
        rw [← reverseIntegral_shuffle hv a t u (j :: w)]
        ring
      have h2 : (fun t =>
          ((shuffles (i :: u) w).map (fun z => reverseIntegral v a z t)).sum * v j t) =
          fun t => reverseIntegral v a (i :: u) t *
            (reverseIntegral v a w t * v j t) := by
        funext t
        rw [← reverseIntegral_shuffle hv a t (i :: u) w]
        ring
      rw [h1, h2]
      linarith
termination_by u.length + w.length

/-- Chronological interleavings, obtained by reversing the internal word convention.
The reversal is explicit, so its multiplicities follow the proven recursion. -/
def chronologicalShuffles {ι : Type*} (u w : List ι) : List (List ι) :=
  (shuffles u.reverse w.reverse).map List.reverse

theorem signature_shuffle {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) (a b : ℝ) (u w : List ι) :
    signature v a b u * signature v a b w =
      ((chronologicalShuffles u w).map (signature v a b)).sum := by
  simpa only [signature, chronologicalShuffles, List.map_map, Function.comp_def,
    List.reverse_reverse] using reverseIntegral_shuffle hv a b u.reverse w.reverse

theorem shuffles_word_length {ι : Type*} (u w z : List ι) (hz : z ∈ shuffles u w) :
    z.length = u.length + w.length := by
  cases u with
  | nil =>
    have he : z = w := by simpa only [shuffles, List.mem_singleton] using hz
    simpa only [List.length_nil, zero_add] using congrArg List.length he
  | cons i u =>
    cases w with
    | nil => simpa [shuffles_nil_right, List.length_cons] using! congrArg List.length (List.mem_singleton.mp
        (by simpa only [shuffles_nil_right] using hz))
    | cons j w =>
      rw [shuffles, List.mem_append] at hz
      rcases hz with h | h
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
        have hlen := shuffles_word_length u (j :: w) q hq
        simp only [List.length_cons] at *
        omega
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
        have hlen := shuffles_word_length (i :: u) w q hq
        simp only [List.length_cons] at *
        omega
termination_by u.length + w.length

theorem chronologicalShuffles_word_length {ι : Type*} (u w z : List ι)
    (hz : z ∈ chronologicalShuffles u w) : z.length = u.length + w.length := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
  simpa only [List.length_reverse] using shuffles_word_length u.reverse w.reverse q hq

end LinearInputCurveWordChen
