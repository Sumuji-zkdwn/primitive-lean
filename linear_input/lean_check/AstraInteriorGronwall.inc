
/-! Endpoint-inclusive Gronwall from interior-only derivatives and closed-interval continuity. -/

namespace KerrKoopman.InteriorGronwall

open Set

theorem energy_envelope (R R' : ℝ → ℝ) (δ η T t : ℝ)
    (hη : 0 ≤ η) (hc : ContinuousOn R (Icc 0 T))
    (hd : ∀ x ∈ Ioo 0 T, HasDerivAt R (R' x) x)
    (hzero : R 0 ≤ δ) (hineq : ∀ x ∈ Ioo 0 T, R' x ≤ 4*R x+η)
    (ht : t ∈ Icc 0 T) : R t ≤ Real.exp (4*t)*(δ+t*η) := by
  let W : ℝ → ℝ := fun x => Real.exp (-4*x)*(R x+η/4)
  have cexp : Continuous (fun x : ℝ => Real.exp (-4*x)) := by fun_prop
  have cW : ContinuousOn W (Icc 0 T) := cexp.continuousOn.mul (hc.add continuousOn_const)
  have dW (x : ℝ) (hx : x ∈ Ioo 0 T) :
      HasDerivAt W (Real.exp (-4*x)*(R' x-4*R x-η)) x := by
    have he : HasDerivAt (fun y : ℝ => Real.exp (-4*y)) (-4*Real.exp (-4*x)) x := by
      convert ((hasDerivAt_id x).const_mul (-4)).exp using 1
      · rfl
      · simp only [id_eq]
        ring
    convert he.mul ((hd x hx).add_const (η/4)) using 1
    ring
  have hanti : AntitoneOn W (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) cW
    · intro x hx
      rw [interior_Icc] at hx
      exact (dW x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(dW x hx).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) (by linarith [hineq x hx])
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hw := hanti ⟨le_rfl,hT⟩ ht ht.1
  dsimp only [W] at hw
  simp only [mul_zero, Real.exp_zero, one_mul] at hw
  have hi : Real.exp (4*t)*Real.exp (-4*t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hm := mul_le_mul_of_nonneg_left hw (Real.exp_nonneg (4*t))
  rw [← mul_assoc, hi, one_mul] at hm
  have hz := mul_le_mul_of_nonneg_left hzero (Real.exp_nonneg (4*t))
  have hg : R t ≤ gronwallBound δ 4 η t := by
    rw [gronwallBound_of_K_ne_0 (by norm_num : (4 : ℝ) ≠ 0)]
    nlinarith
  exact hg.trans (StoppingCertificate.gronwall_four_le_envelope δ η t hη)

/-- A rational short-time budget needs only exp(1)<3, not numerical exp evaluation. -/
theorem short_time_energy_budget (R q t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1/5)
    (hR : R ≤ Real.exp (4*t)*((2/25 : ℝ)+t*(12/5))*q^2) : R ≤ 2*q^2 := by
  have he : Real.exp (4*t) ≤ 3 :=
    (Real.exp_le_exp.mpr (by linarith)).trans Real.exp_one_lt_three.le
  have hc : 0 ≤ (2/25 : ℝ)+t*(12/5) := by positivity
  have hb : (2/25 : ℝ)+t*(12/5) ≤ 14/25 := by linarith
  have hm := mul_le_mul he hb hc (by norm_num : (0 : ℝ) ≤ 3)
  have hp := mul_le_mul_of_nonneg_right hm (sq_nonneg q)
  nlinarith [sq_nonneg q]

theorem short_time_restored_budget (error R q t : ℝ) (hq : 0 ≤ q)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1/5)
    (herror : error^2 ≤ 2*R)
    (hR : R ≤ Real.exp (4*t)*((2/25 : ℝ)+t*(12/5))*q^2) : error ≤ 2*q := by
  have hr := short_time_energy_budget R q t ht0 ht1 hR
  nlinarith [sq_nonneg (error-2*q)]

/-- The sharper width-one-half initial tail is valid also at N=0. -/
theorem initial_tail_budget (N : ℕ) :
    (149/98 : ℝ)*(57/250 : ℝ)^2*Real.exp (-((N : ℝ)+1)) ≤
      (2/25 : ℝ)*(Real.exp (-(3/20 : ℝ)*((N : ℝ)+1)))^2 := by
  have he : -((N : ℝ)+1) ≤ -(3/10 : ℝ)*((N : ℝ)+1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hm := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
    (by norm_num : (0 : ℝ) ≤ (149/98 : ℝ)*(57/250 : ℝ)^2)
  have hid : (Real.exp (-(3/20 : ℝ)*((N : ℝ)+1)))^2 =
      Real.exp (-(3/10 : ℝ)*((N : ℝ)+1)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hid]
  nlinarith [Real.exp_pos (-(3/10 : ℝ)*((N : ℝ)+1))]

end KerrKoopman.InteriorGronwall
