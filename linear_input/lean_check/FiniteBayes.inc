/-! Finite Bayesian weights, exponential tilts, and transport through observations. -/

noncomputable section
open Real Finset

namespace LinearInputBayes

attribute [local instance] Classical.propDecidable

def mass {α : Type*} [Fintype α] (w : α → ℝ) : ℝ := ∑ x, w x

def IsDistribution {α : Type*} [Fintype α] (w : α → ℝ) : Prop :=
  (∀ x, 0 ≤ w x) ∧ mass w = 1

def normalize {α : Type*} [Fintype α] (w : α → ℝ) (x : α) : ℝ := w x / mass w

def posterior {α : Type*} [Fintype α] (w L : α → ℝ) : α → ℝ :=
  normalize (fun x => w x * L x)

def tilt {α : Type*} [Fintype α] (w : α → ℝ) (β : ℝ) (r : α → ℝ) : α → ℝ :=
  posterior w (fun x => exp (β * r x))

theorem mass_scale {α : Type*} [Fintype α] (c : ℝ) (w : α → ℝ) :
    mass (fun x => c * w x) = c * mass w := by simp [mass, Finset.mul_sum]

theorem mass_div {α : Type*} [Fintype α] (w : α → ℝ) (c : ℝ) :
    mass (fun x => w x / c) = mass w / c := by simp [mass, Finset.sum_div]

theorem normalize_mass {α : Type*} [Fintype α] {w : α → ℝ} (h : mass w ≠ 0) :
    mass (normalize w) = 1 := by
  change mass (fun x => w x / mass w) = 1
  rw [mass_div, div_self h]

theorem normalize_of_mass_one {α : Type*} [Fintype α] {w : α → ℝ} (h : mass w = 1) :
    normalize w = w := by funext x; simp [normalize, h]

theorem normalize_distribution {α : Type*} [Fintype α] {w : α → ℝ}
    (hw : ∀ x, 0 ≤ w x) (h : 0 < mass w) : IsDistribution (normalize w) := by
  exact ⟨fun x => div_nonneg (hw x) h.le, normalize_mass h.ne'⟩

theorem posterior_distribution {α : Type*} [Fintype α] {w L : α → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hL : ∀ x, 0 ≤ L x)
    (h : 0 < mass (fun x => w x * L x)) : IsDistribution (posterior w L) :=
  normalize_distribution (fun x => mul_nonneg (hw x) (hL x)) h

theorem posterior_zero_prior {α : Type*} [Fintype α] (w L : α → ℝ) {x : α}
    (h : w x = 0) : posterior w L x = 0 := by simp [posterior, normalize, h]

theorem zero_evidence_not_distribution {α : Type*} [Fintype α] (w L : α → ℝ)
    (h : mass (fun x => w x * L x) = 0) : ¬ IsDistribution (posterior w L) := by
  intro hp
  have hm := hp.2
  change mass (fun x => w x * L x / mass (fun y => w y * L y)) = 1 at hm
  rw [mass_div, h] at hm
  norm_num at hm

theorem mixture_log_loss_bound {α : Type*} [Fintype α] {w L : α → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hL : ∀ x, 0 ≤ L x) {x : α}
    (hx : 0 < w x) (hLx : 0 < L x) :
    -log (mass (fun y => w y * L y)) + log (L x) ≤ log (1 / w x) := by
  have hle : w x * L x ≤ mass (fun y => w y * L y) :=
    Finset.single_le_sum (fun y _ => mul_nonneg (hw y) (hL y)) (Finset.mem_univ x)
  have hlog := Real.log_le_log (mul_pos hx hLx) hle
  rw [Real.log_mul hx.ne' hLx.ne'] at hlog
  rw [one_div, Real.log_inv]
  linarith

theorem posterior_zero_iff {α : Type*} [Fintype α] (w L : α → ℝ)
    (h : mass (fun x => w x * L x) ≠ 0) (x : α) :
    posterior w L x = 0 ↔ w x = 0 ∨ L x = 0 := by
  simp [posterior, normalize, div_eq_zero_iff, h, mul_eq_zero]

theorem normalize_scale {α : Type*} [Fintype α] {c : ℝ} (hc : c ≠ 0) (w : α → ℝ) :
    normalize (fun x => c * w x) = normalize w := by
  funext x
  simp only [normalize, mass_scale]
  exact mul_div_mul_left (w x) (mass w) hc

theorem posterior_compose {α : Type*} [Fintype α] (w L M : α → ℝ)
    (h : mass (fun x => w x * L x) ≠ 0) :
    posterior (posterior w L) M = posterior w (fun x => L x * M x) := by
  change normalize (fun x => normalize (fun y => w y * L y) x * M x) = _
  calc
    _ = normalize (fun x => (mass (fun y => w y * L y))⁻¹ * (w x * (L x * M x))) := by
      congr 1; funext x; simp only [normalize, div_eq_mul_inv]; ring
    _ = _ := normalize_scale (inv_ne_zero h) _

theorem posterior_commute {α : Type*} [Fintype α] (w L M : α → ℝ)
    (hL : mass (fun x => w x * L x) ≠ 0) (hM : mass (fun x => w x * M x) ≠ 0) :
    posterior (posterior w L) M = posterior (posterior w M) L := by
  rw [posterior_compose w L M hL, posterior_compose w M L hM]
  congr 1; funext x; ring

theorem distribution_has_positive {α : Type*} [Fintype α] {w : α → ℝ}
    (hw : IsDistribution w) : ∃ x, 0 < w x := by
  classical
  by_contra h
  have hn : ∀ x, w x ≤ 0 := fun x => le_of_not_gt (fun hx => h ⟨x, hx⟩)
  have hm : mass w ≤ 0 := Finset.sum_nonpos (fun x _ => hn x)
  rw [hw.2] at hm
  norm_num at hm

theorem positive_likelihood_evidence {α : Type*} [Fintype α] {w L : α → ℝ}
    (hw : IsDistribution w) (hL : ∀ x, 0 < L x) : 0 < mass (fun x => w x * L x) := by
  obtain ⟨x, hx⟩ := distribution_has_positive hw
  exact lt_of_lt_of_le (mul_pos hx (hL x))
    (Finset.single_le_sum (fun y _ => mul_nonneg (hw.1 y) (hL y).le) (Finset.mem_univ x))

theorem tilt_distribution {α : Type*} [Fintype α] {w : α → ℝ}
    (hw : IsDistribution w) (β : ℝ) (r : α → ℝ) : IsDistribution (tilt w β r) :=
  posterior_distribution hw.1 (fun _ => (exp_pos _).le)
    (positive_likelihood_evidence hw (fun _ => exp_pos _))

theorem tilt_zero {α : Type*} [Fintype α] {w : α → ℝ}
    (hw : IsDistribution w) (r : α → ℝ) : tilt w 0 r = w := by
  simpa only [tilt, posterior, zero_mul, exp_zero, mul_one] using normalize_of_mass_one hw.2

theorem tilt_add {α : Type*} [Fintype α] {w : α → ℝ}
    (hw : IsDistribution w) (β γ : ℝ) (r : α → ℝ) :
    tilt (tilt w β r) γ r = tilt w (β + γ) r := by
  unfold tilt
  rw [posterior_compose w _ _ (positive_likelihood_evidence hw (fun _ => exp_pos _)).ne']
  congr 1; funext x; rw [add_mul, exp_add]

theorem tilt_cancel {α : Type*} [Fintype α] {w : α → ℝ}
    (hw : IsDistribution w) (β : ℝ) (r : α → ℝ) : tilt (tilt w β r) (-β) r = w := by
  rw [tilt_add hw, add_neg_cancel, tilt_zero hw]

theorem tilt_support {α : Type*} [Fintype α] {w : α → ℝ}
    (hw : IsDistribution w) (β : ℝ) (r : α → ℝ) (x : α) :
    tilt w β r x = 0 ↔ w x = 0 := by
  rw [tilt, posterior_zero_iff _ _ (positive_likelihood_evidence hw (fun _ => exp_pos _)).ne']
  simp [exp_ne_zero]

def pushWeight {α β : Type*} [Fintype α] (f : α → β) (w : α → ℝ) (b : β) : ℝ :=
  ∑ x, if f x = b then w x else 0

theorem push_mass {α β : Type*} [Fintype α] [Fintype β] (f : α → β) (w : α → ℝ) :
    mass (pushWeight f w) = mass w := by
  simp only [mass, pushWeight]
  rw [Finset.sum_comm]
  simp

theorem push_distribution {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) {w : α → ℝ} (hw : IsDistribution w) : IsDistribution (pushWeight f w) := by
  refine ⟨fun b => Finset.sum_nonneg (fun x _ => ?_), ?_⟩
  · split_ifs <;> simp [hw.1]
  · rw [push_mass, hw.2]

theorem push_div {α β : Type*} [Fintype α] (f : α → β) (w : α → ℝ) (c : ℝ) :
    pushWeight f (fun x => w x / c) = fun b => pushWeight f w b / c := by
  funext b
  simp only [pushWeight, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

theorem push_normalize {α β : Type*} [Fintype α] [Fintype β] (f : α → β) (w : α → ℝ) :
    pushWeight f (normalize w) = normalize (pushWeight f w) := by
  unfold normalize
  rw [push_div, push_mass]

theorem push_weight_likelihood {α β : Type*} [Fintype α]
    (f : α → β) (w : α → ℝ) (L : β → ℝ) :
    pushWeight f (fun x => w x * L (f x)) = fun b => pushWeight f w b * L b := by
  funext b
  simp only [pushWeight, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : f x = b <;> simp [h]

/-- A likelihood depending only on the retained observation commutes with forgetting. -/
theorem push_posterior {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (w : α → ℝ) (L : β → ℝ) :
    pushWeight f (posterior w (fun x => L (f x))) = posterior (pushWeight f w) L := by
  unfold posterior
  rw [push_normalize, push_weight_likelihood]

theorem push_evidence {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (w : α → ℝ) (L : β → ℝ) :
    mass (fun b => pushWeight f w b * L b) = mass (fun x => w x * L (f x)) := by
  rw [← push_weight_likelihood, push_mass]

theorem branchZero_posterior (m : ℕ) (w : Fin (2 * m + 1) → ℝ)
    (L : Fin (2 * m + 1) → ℝ) :
    pushWeight (LinearInputF0.branchZeroK m)
        (posterior w (fun x => L (LinearInputF0.branchZeroK m x))) =
      posterior (pushWeight (LinearInputF0.branchZeroK m) w) L := push_posterior _ _ _

theorem branchPi_posterior (m : ℕ) (w : Fin (2 * m + 1) → ℝ)
    (L : Fin (2 * m + 1) → ℝ) :
    pushWeight (LinearInputF0.branchPiK m)
        (posterior w (fun x => L (LinearInputF0.branchPiK m x))) =
      posterior (pushWeight (LinearInputF0.branchPiK m) w) L := push_posterior _ _ _

theorem curve_weight_as_tilt {α : Type*} [Fintype α] (w : α → ℝ)
    (β : ℝ) (ε : ℝ → ℝ) (θ : α → ℝ → ℝ) (ℓ : ℝ) :
    posterior w (fun x => Elastica.exponentialWeight β ε (θ x) ℓ) =
      tilt w (-β) (fun x => Elastica.energy ε (θ x) ℓ) := rfl

theorem curve_weight_distribution {α : Type*} [Fintype α] {w : α → ℝ}
    (hw : IsDistribution w) (β : ℝ) (ε : ℝ → ℝ) (θ : α → ℝ → ℝ) (ℓ : ℝ) :
    IsDistribution (posterior w (fun x => Elastica.exponentialWeight β ε (θ x) ℓ)) := by
  rw [curve_weight_as_tilt]
  exact tilt_distribution hw _ _

theorem curve_split_update {α : Type*} [Fintype α] {w : α → ℝ}
    (hw : IsDistribution w) {ε : ℝ → ℝ} {θ : α → ℝ → ℝ}
    (hε : Continuous ε) (hθ : ∀ x, ContDiff ℝ 1 (θ x)) (β a ℓ : ℝ) :
    posterior w (fun x => Elastica.exponentialWeight β ε (θ x) ℓ) =
      posterior (posterior w (fun x => Elastica.exponentialWeight β ε (θ x) a))
        (fun x => exp (-β * (∫ s in a..ℓ, ε (deriv (θ x) s)))) := by
  rw [posterior_compose w _ _
    (positive_likelihood_evidence hw (fun x => Elastica.exponentialWeight_pos β ε (θ x) a)).ne']
  congr 1; funext x
  exact Elastica.exponentialWeight_split hε (hθ x) β a ℓ

end LinearInputBayes
