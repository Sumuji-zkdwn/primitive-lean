/-! The even orders with an odd factor admit an explicit return with opposite tangent. -/

namespace RobotFacingOrders

open LinearInputCurveWordAlgebra LinearInputCurveWordArc LinearInputRobotWalkArc
open LinearInputRobotWalkLengths

private noncomputable abbrev pos (h a : ℝ) (w : List Bool) := endpoint (arcWord h a w)
private noncomputable abbrev face (h a : ℝ) (w : List Bool) := rotation (angle (arcWord h a w))

private theorem pos_append (h a : ℝ) (u v : List Bool) :
    pos h a (u ++ v) = pos h a u + face h a u * pos h a v := by
  simp only [pos, face, arcWord_append, join_endpoint]

private theorem face_append (h a : ℝ) (u v : List Bool) :
    face h a (u ++ v) = face h a u * face h a v := by
  simp only [face, arcWord_append, join_angle, rotation_add]

/-- The forward and backward runs of d arcs traverse the same set of small edges. -/
private theorem macro_steps {h a : ℝ} (hh : 0 < h) (ha : a ≠ 0) (d : ℕ)
    (hz1 : rotation a ≠ 1) :
    face h a (copies [true] d) = (rotation a) ^ d ∧
    face h a (copies [false] d) = ((rotation a) ^ d)⁻¹ ∧
    pos h a (copies [false] d) = ((rotation a) ^ d)⁻¹ * pos h a (copies [true] d) := by
  let z := rotation a
  have hz : z ≠ 0 := Complex.exp_ne_zero _
  have hneg : rotation (-a) = z⁻¹ := by simp [z, rotation, neg_mul, Complex.exp_neg]
  have hp : face h a [true] = z := by simp [face, angle_arcWord hh ha, turns, z]
  have hm : face h a [false] = z⁻¹ := by simpa [face, angle_arcWord hh ha, turns] using hneg
  have he : pos h a [false] = z⁻¹ * pos h a [true] := by
    simpa [pos, arcWord, join_empty, hneg] using negative_chord hh ha
  obtain ⟨rf, ef⟩ := copies_state h a [true] d
  obtain ⟨rb, eb⟩ := copies_state h a [false] d
  change face h a _ = face h a [true] ^ d at rf
  change face h a _ = face h a [false] ^ d at rb
  change pos h a _ = (∑ i ∈ Finset.range d, face h a [true] ^ i) * pos h a [true] at ef
  change pos h a _ = (∑ i ∈ Finset.range d, face h a [false] ^ i) * pos h a [false] at eb
  rw [hp] at rf ef
  rw [hm, inv_pow] at rb
  rw [hm, he] at eb
  refine ⟨rf, rb, ?_⟩
  change pos h a _ = (z ^ d)⁻¹ * pos h a _
  have hzone : z ≠ 1 := hz1
  rw [eb, ef, geom_sum_inv hzone hz, geom_sum_eq hzone, inv_pow]
  have hzdm : z ^ d ≠ 0 := pow_ne_zero _ hz
  field_simp [hz, hzdm, sub_ne_zero.mpr hzone]

/-- At order 2*m*d with m=2*k+1, F is d left turns and B is d right turns.
The block F F B F advances by two macro-edges and traverses the second one three times. -/
def reversalWord (k d : ℕ) : List Bool :=
  let f := copies [true] d
  let b := copies [false] d
  let m := 2 * k + 1
  copies f m ++ (copies (f ++ (f ++ (b ++ f))) k ++ copies f (m + 1))

private theorem half_turn_polynomial {x : ℂ} {k : ℕ} (kpos : 0 < k)
    (hx : IsPrimitiveRoot x (2 * (2*k + 1))) :
    let m := 2*k + 1
    let g := fun (r : ℂ) (n : ℕ) => ∑ i ∈ Finset.range n, r ^ i
    x^m = -1 ∧ x^m * ((x^2)^k * x^(m+1)) = -1 ∧
    g x m + x^m * (g (x^2) k * (1+3*x) + (x^2)^k * g x (m+1)) = 0 := by
  dsimp only
  let m := 2*k + 1
  have hm : 0 < m := by dsimp [m]; omega
  have hn : 1 < 2*m := by omega
  have hx0 := hx.ne_zero (by dsimp [m] at *; omega)
  have hx1 := hx.ne_one hn
  have hx2 : x^2 ≠ 1 := hx.pow_ne_one_of_pos_of_lt (by decide) (by dsimp [m] at *; omega)
  have hhalf : x^m = -1 := by
    have h2 : (x^m)^2 = 1 := by rw [← pow_mul, Nat.mul_comm m 2]; exact hx.pow_eq_one
    exact (sq_eq_one_iff.mp h2).resolve_left
      (hx.pow_ne_one_of_pos_of_lt hm.ne' (show m < 2*m by omega))
  have hbetween : (x^2)^k = -x⁻¹ := by
    rw [← pow_mul]
    apply (mul_left_inj' hx0).mp
    rw [← pow_succ, show 2 * k + 1 = m from rfl, hhalf]
    field_simp
  have hafter : x^(m+1) = -x := by rw [pow_succ, hhalf, neg_one_mul]
  change x^m = -1 ∧ x^m * ((x^2)^k * x^(m+1)) = -1 ∧ _
  refine ⟨hhalf, ?_, ?_⟩
  · rw [hhalf, hbetween, hafter]
    field_simp
  · change (∑ i ∈ Finset.range m, x^i) + x^m *
      ((∑ i ∈ Finset.range k, (x^2)^i) * (1+3*x) +
      (x^2)^k * ∑ i ∈ Finset.range (m+1), x^i) = 0
    rw [geom_sum_eq hx1, geom_sum_eq hx2, geom_sum_eq hx1, hhalf, hbetween, hafter]
    field_simp [hx0, sub_ne_zero.mpr hx1, sub_ne_zero.mpr hx2]
    ring

theorem even_factor_reversal {k d : ℕ} (hk : 0 < k) (hd : 0 < d)
    {h : ℝ} (hh : 0 < h) :
    let N := 2 * (2*k+1) * d
    endpoint (arcWord h (2 * Real.pi / N) (reversalWord k d)) = 0 ∧
      rotation (angle (arcWord h (2 * Real.pi / N) (reversalWord k d))) = -1 := by
  let m := 2*k + 1
  let N := (2*m) * d
  let a : ℝ := 2 * Real.pi / N
  let z := rotation a
  let x := z^d
  let f := copies [true] d
  let b := copies [false] d
  let v := f ++ (f ++ (b ++ f))
  have hN : 1 < N := by
    have hm : 1 < 2*m := by dsimp [m]; omega
    exact lt_of_lt_of_le hm (Nat.le_mul_of_pos_right _ hd)
  have ha : a ≠ 0 := by dsimp [a]; positivity
  have hz : IsPrimitiveRoot z N := step_root_primitive N (by omega)
  have hx : IsPrimitiveRoot x (2*m) := by
    simpa [x, N, Nat.mul_div_cancel _ hd] using
      (hz.pow_of_dvd hd.ne' (dvd_mul_left d (2*m)))
  have hx0 : x ≠ 0 := hx.ne_zero (by dsimp [m]; omega)
  obtain ⟨hf, hb, he⟩ := macro_steps hh ha d (hz.ne_one hN)
  change face h a f = x at hf
  change face h a b = x⁻¹ at hb
  change pos h a b = x⁻¹ * pos h a f at he
  have hv : face h a v = x^2 := by
    simp only [v, face_append, hf, hb]
    field_simp
  have hev : pos h a v = (1+3*x) * pos h a f := by
    simp only [v, pos_append, hf, hb, he]
    field_simp
    ring
  obtain ⟨_, hrot, hsum⟩ := half_turn_polynomial hk hx
  change pos h a (copies f m ++ (copies v k ++ copies f (m+1))) = 0 ∧
    face h a (copies f m ++ (copies v k ++ copies f (m+1))) = -1
  have ep (u : List Bool) (n : ℕ) : pos h a (copies u n) =
      (∑ i ∈ Finset.range n, face h a u ^ i) * pos h a u := (copies_state h a u n).2
  have fr (u : List Bool) (n : ℕ) : face h a (copies u n) = face h a u ^ n :=
    (copies_state h a u n).1
  simp only [pos_append, face_append, ep, fr, hv, hev, hf]
  exact ⟨by linear_combination pos h a f * hsum, hrot⟩

/-- The exact orders above one for which every returning position restores the tangent. -/
theorem facing_for_all_closed_iff {N : ℕ} (hN : 1 < N) {h : ℝ} (hh : 0 < h) :
    (∀ w : List Bool, endpoint (arcWord h (2 * Real.pi / N) w) = 0 →
      rotation (angle (arcWord h (2 * Real.pi / N) w)) = 1) ↔
    Odd N ∨ ∃ b : ℕ, N = 2^b := by
  constructor
  · intro hall
    obtain ⟨a, m, hm, hfactor⟩ := Nat.exists_eq_two_pow_mul_odd (show N ≠ 0 by omega)
    cases a with
    | zero => left; simpa [hfactor] using hm
    | succ a =>
      by_cases h1 : m = 1
      · exact Or.inr ⟨a+1, by simpa [h1] using hfactor⟩
      obtain ⟨k, hk⟩ := hm
      have hk0 : 0 < k := by omega
      have horder : N = 2 * (2*k+1) * 2^a := by rw [hfactor, hk, pow_succ]; ring
      obtain ⟨hc, hr⟩ := even_factor_reversal hk0 (pow_pos (by decide : 0 < 2) a) hh
      rw [← horder] at hc hr
      have hbad := (hall _ hc).symm.trans hr
      norm_num at hbad
  · rintro (hodd | ⟨b, rfl⟩)
    · exact fun w hc => RobotFacingOdd.facing_of_closed_odd hN hodd hh w hc
    · cases b with
      | zero => simp at hN
      | succ b =>
        exact LinearInputRobotWalkClassification.facing_of_closed 2 b Nat.prime_two hh

end RobotFacingOrders
