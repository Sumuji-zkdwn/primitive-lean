/-!
Derived low-order history observations of the actual primitive curve.

This supplement uses Elastica's reconstructed coordinates and the existing
signed-area functional. It does not assume Chen's theorem or Hambly--Lyons,
and it does not identify a finite observation vector with a full signature.
-/

noncomputable section
open Real Set MeasureTheory

namespace LinearInputHistorySignature

/-- The xy component of the second iterated integral for the reconstructed curve. -/
def secondXY (θ : ℝ → ℝ) (ℓ : ℝ) : ℝ :=
  ∫ s in 0..ℓ, Elastica.xCoord θ 0 s * sin (θ s)

/-- The yx component of the second iterated integral for the reconstructed curve. -/
def secondYX (θ : ℝ → ℝ) (ℓ : ℝ) : ℝ :=
  ∫ s in 0..ℓ, Elastica.yCoord θ 0 s * cos (θ s)

def secondXX (θ : ℝ → ℝ) (ℓ : ℝ) : ℝ :=
  ∫ s in 0..ℓ, Elastica.xCoord θ 0 s * cos (θ s)

def secondYY (θ : ℝ → ℝ) (ℓ : ℝ) : ℝ :=
  ∫ s in 0..ℓ, Elastica.yCoord θ 0 s * sin (θ s)

theorem secondXY_eq_iterated (θ : ℝ → ℝ) (ℓ : ℝ) :
    secondXY θ ℓ = ∫ s in 0..ℓ, (∫ t in 0..s, cos (θ t)) * sin (θ s) := by
  simp only [secondXY, Elastica.xCoord, zero_add]

theorem secondYX_eq_iterated (θ : ℝ → ℝ) (ℓ : ℝ) :
    secondYX θ ℓ = ∫ s in 0..ℓ, (∫ t in 0..s, sin (θ t)) * cos (θ s) := by
  simp only [secondYX, Elastica.yCoord, zero_add]

theorem xCoord_continuous {θ : ℝ → ℝ} (hθ : Continuous θ) :
    Continuous (Elastica.xCoord θ 0) := by
  exact (show Differentiable ℝ (Elastica.xCoord θ 0) from
    fun s => (Elastica.hasDerivAt_xCoord hθ 0 s).differentiableAt).continuous

theorem yCoord_continuous {θ : ℝ → ℝ} (hθ : Continuous θ) :
    Continuous (Elastica.yCoord θ 0) := by
  exact (show Differentiable ℝ (Elastica.yCoord θ 0) from
    fun s => (Elastica.hasDerivAt_yCoord hθ 0 s).differentiableAt).continuous

/-- The area already defined by primitive is the antisymmetric second level. -/
theorem area_eq_second_antisymmetric {θ : ℝ → ℝ} (hθ : Continuous θ) (ℓ : ℝ) :
    LinearInputAreaVariation.area θ ℓ = (secondXY θ ℓ - secondYX θ ℓ) / 2 := by
  unfold LinearInputAreaVariation.area secondXY secondYX
  have hxy : IntervalIntegrable
      (fun s => Elastica.xCoord θ 0 s * sin (θ s)) volume 0 ℓ :=
    ((xCoord_continuous hθ).mul (continuous_sin.comp hθ)).intervalIntegrable 0 ℓ
  have hyx : IntervalIntegrable
      (fun s => Elastica.yCoord θ 0 s * cos (θ s)) volume 0 ℓ :=
    ((yCoord_continuous hθ).mul (continuous_cos.comp hθ)).intervalIntegrable 0 ℓ
  rw [intervalIntegral.integral_sub hxy hyx]
  ring

/-- The degree-two shuffle relation follows by integration by parts. -/
theorem second_shuffle {θ : ℝ → ℝ} (hθ : Continuous θ) (ℓ : ℝ) :
    secondXY θ ℓ + secondYX θ ℓ =
      Elastica.xCoord θ 0 ℓ * Elastica.yCoord θ 0 ℓ := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun s _ => Elastica.hasDerivAt_xCoord hθ 0 s)
    (fun s _ => Elastica.hasDerivAt_yCoord hθ 0 s)
    ((continuous_cos.comp hθ).intervalIntegrable 0 ℓ)
    ((continuous_sin.comp hθ).intervalIntegrable 0 ℓ)
  simp only [Elastica.xCoord_zero, Elastica.yCoord_zero, mul_zero, sub_zero] at h
  have h' : secondXY θ ℓ =
      Elastica.xCoord θ 0 ℓ * Elastica.yCoord θ 0 ℓ - secondYX θ ℓ := by
    simpa only [secondXY, secondYX, mul_comm] using h
  linarith

theorem secondXX_eq_half_square {θ : ℝ → ℝ} (hθ : Continuous θ) (ℓ : ℝ) :
    secondXX θ ℓ = (Elastica.xCoord θ 0 ℓ) ^ 2 / 2 := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun s _ => Elastica.hasDerivAt_xCoord hθ 0 s)
    (fun s _ => Elastica.hasDerivAt_xCoord hθ 0 s)
    ((continuous_cos.comp hθ).intervalIntegrable 0 ℓ)
    ((continuous_cos.comp hθ).intervalIntegrable 0 ℓ)
  simp only [Elastica.xCoord_zero, mul_zero, sub_zero] at h
  have h' : secondXX θ ℓ =
      Elastica.xCoord θ 0 ℓ * Elastica.xCoord θ 0 ℓ - secondXX θ ℓ := by
    simpa only [secondXX, mul_comm] using h
  nlinarith

theorem secondYY_eq_half_square {θ : ℝ → ℝ} (hθ : Continuous θ) (ℓ : ℝ) :
    secondYY θ ℓ = (Elastica.yCoord θ 0 ℓ) ^ 2 / 2 := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun s _ => Elastica.hasDerivAt_yCoord hθ 0 s)
    (fun s _ => Elastica.hasDerivAt_yCoord hθ 0 s)
    ((continuous_sin.comp hθ).intervalIntegrable 0 ℓ)
    ((continuous_sin.comp hθ).intervalIntegrable 0 ℓ)
  simp only [Elastica.yCoord_zero, mul_zero, sub_zero] at h
  have h' : secondYY θ ℓ =
      Elastica.yCoord θ 0 ℓ * Elastica.yCoord θ 0 ℓ - secondYY θ ℓ := by
    simpa only [secondYY, mul_comm] using h
  nlinarith

/-- Endpoint and signed area recover every degree-two coordinate. -/
theorem mixed_second_reconstruction {θ : ℝ → ℝ} (hθ : Continuous θ) (ℓ : ℝ) :
    secondXY θ ℓ =
      Elastica.xCoord θ 0 ℓ * Elastica.yCoord θ 0 ℓ / 2 +
        LinearInputAreaVariation.area θ ℓ ∧
    secondYX θ ℓ =
      Elastica.xCoord θ 0 ℓ * Elastica.yCoord θ 0 ℓ / 2 -
        LinearInputAreaVariation.area θ ℓ := by
  have hs := second_shuffle hθ ℓ
  have ha := area_eq_second_antisymmetric hθ ℓ
  constructor <;> linarith

/-- Area of a subarc after translating its starting point to the origin. -/
def subarcArea (θ : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (1 / 2) * ∫ s in a..b,
    (Elastica.xCoord θ 0 s - Elastica.xCoord θ 0 a) * sin (θ s) -
    (Elastica.yCoord θ 0 s - Elastica.yCoord θ 0 a) * cos (θ s)

/-- The second-level cross term is derived from splitting the actual area integral. -/
theorem area_split_cross_term {θ : ℝ → ℝ} (hθ : Continuous θ) (a b : ℝ) :
    LinearInputAreaVariation.area θ b =
      LinearInputAreaVariation.area θ a + subarcArea θ a b +
      (Elastica.xCoord θ 0 a * (Elastica.yCoord θ 0 b - Elastica.yCoord θ 0 a) -
       Elastica.yCoord θ 0 a * (Elastica.xCoord θ 0 b - Elastica.xCoord θ 0 a)) / 2 := by
  let f := fun s => Elastica.xCoord θ 0 s * sin (θ s) -
    Elastica.yCoord θ 0 s * cos (θ s)
  have hf : Continuous f :=
    ((xCoord_continuous hθ).mul (continuous_sin.comp hθ)).sub
      ((yCoord_continuous hθ).mul (continuous_cos.comp hθ))
  have hs : (∫ s in 0..a, f s) + (∫ s in a..b, f s) = ∫ s in 0..b, f s :=
    intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable 0 a) (hf.intervalIntegrable a b)
  have hx := Elastica.xCoord_sub_eq_integral hθ 0 a b
  have hy := Elastica.yCoord_sub_eq_integral hθ 0 a b
  have hfi : IntervalIntegrable f volume a b := hf.intervalIntegrable a b
  have hxs : IntervalIntegrable
      (fun s => Elastica.xCoord θ 0 a * sin (θ s)) volume a b :=
    (continuous_const.mul (continuous_sin.comp hθ)).intervalIntegrable a b
  have hyc : IntervalIntegrable
      (fun s => Elastica.yCoord θ 0 a * cos (θ s)) volume a b :=
    (continuous_const.mul (continuous_cos.comp hθ)).intervalIntegrable a b
  have hsub : IntervalIntegrable
      (fun s => f s - Elastica.xCoord θ 0 a * sin (θ s)) volume a b := hfi.sub hxs
  have hg : (fun s =>
      (Elastica.xCoord θ 0 s - Elastica.xCoord θ 0 a) * sin (θ s) -
      (Elastica.yCoord θ 0 s - Elastica.yCoord θ 0 a) * cos (θ s)) =
      fun s => f s - Elastica.xCoord θ 0 a * sin (θ s) +
        Elastica.yCoord θ 0 a * cos (θ s) := by
    funext s
    dsimp [f]
    ring
  have hi : (∫ s in a..b,
      (Elastica.xCoord θ 0 s - Elastica.xCoord θ 0 a) * sin (θ s) -
      (Elastica.yCoord θ 0 s - Elastica.yCoord θ 0 a) * cos (θ s)) =
      (∫ s in a..b, f s) -
      Elastica.xCoord θ 0 a * (∫ s in a..b, sin (θ s)) +
      Elastica.yCoord θ 0 a * (∫ s in a..b, cos (θ s)) := by
    rw [hg, intervalIntegral.integral_add hsub hyc]
    rw [intervalIntegral.integral_sub hfi hxs]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  unfold LinearInputAreaVariation.area subarcArea
  change (1 / 2) * (∫ s in 0..b, f s) = _
  rw [hi, ← hx, ← hy]
  dsimp [f] at hs ⊢
  linarith [hs]

/-- Joining a rotated second piece uses the already-proved coordinate rotation. -/
theorem rotated_piece_endpoint_x {θ : ℝ → ℝ} (hθ : Continuous θ)
    (α x ℓ : ℝ) :
    Elastica.xCoord (fun s => θ s + α) x ℓ =
      x + cos α * Elastica.xCoord θ 0 ℓ - sin α * Elastica.yCoord θ 0 ℓ := by
  have h := Elastica.xCoord_add_angle hθ α 0 0 x ℓ
  simp only [sub_zero] at h
  linarith

theorem rotated_piece_endpoint_y {θ : ℝ → ℝ} (hθ : Continuous θ)
    (α y ℓ : ℝ) :
    Elastica.yCoord (fun s => θ s + α) y ℓ =
      y + sin α * Elastica.xCoord θ 0 ℓ + cos α * Elastica.yCoord θ 0 ℓ := by
  have h := Elastica.yCoord_add_angle hθ α 0 0 y ℓ
  simp only [sub_zero] at h
  linarith

/-- Two inputs to the new observable use the existing observation theorem unchanged. -/
theorem two_inputs_determine_area {S : Type*} (base : S → ℝ)
    (angle : S → ℝ → ℝ) (length : S → ℝ) (p q : S)
    (u v : ℝ) (huv : u ≠ v) :
    (LinearInputObservation.energy base
        (fun z => LinearInputAreaVariation.area (angle z) (length z)) u p =
      LinearInputObservation.energy base
        (fun z => LinearInputAreaVariation.area (angle z) (length z)) u q ∧
     LinearInputObservation.energy base
        (fun z => LinearInputAreaVariation.area (angle z) (length z)) v p =
      LinearInputObservation.energy base
        (fun z => LinearInputAreaVariation.area (angle z) (length z)) v q) ↔
    base p = base q ∧
      LinearInputAreaVariation.area (angle p) (length p) =
      LinearInputAreaVariation.area (angle q) (length q) := by
  exact LinearInputObservation.two_inputs_iff_pair base
    (fun z => LinearInputAreaVariation.area (angle z) (length z)) p q u v huv

/-- An observation hierarchy; it need not be a signature or a cognition model. -/
def agreeThrough {S : Type*} {O : ℕ → Type*}
    (obs : (k : ℕ) → S → O k) (m : ℕ) (x y : S) : Prop :=
  ∀ k, k ≤ m → obs k x = obs k y

theorem agreeThrough_mono {S : Type*} {O : ℕ → Type*}
    (obs : (k : ℕ) → S → O k) {m n : ℕ} {x y : S}
    (hmn : m ≤ n) (h : agreeThrough obs n x y) : agreeThrough obs m x y := by
  intro k hk
  exact h k (hk.trans hmn)

theorem distinguishing_level_refutes_agreement {S : Type*} {O : ℕ → Type*}
    (obs : (k : ℕ) → S → O k) {m k : ℕ} {x y : S}
    (hkm : k ≤ m) (hne : obs k x ≠ obs k y) : ¬ agreeThrough obs m x y := by
  intro h
  exact hne (h k hkm)

theorem all_truncations_iff_all_levels {S : Type*} {O : ℕ → Type*}
    (obs : (k : ℕ) → S → O k) (x y : S) :
    (∀ m, agreeThrough obs m x y) ↔ ∀ k, obs k x = obs k y := by
  exact ⟨fun h k => h k k le_rfl, fun h _ k _ => h k⟩

/-- A finite family separated by some levels is separated at one finite cutoff.
The separating hypothesis is explicit; no signature uniqueness is assumed. -/
theorem finite_family_separating_cutoff {S : Type*} [Fintype S]
    {O : ℕ → Type*} (obs : (k : ℕ) → S → O k)
    (hsep : ∀ x y : S, x ≠ y → ∃ k, obs k x ≠ obs k y) :
    ∃ m, ∀ x y : S, agreeThrough obs m x y → x = y := by
  classical
  let depth : S × S → ℕ := fun p =>
    if h : p.1 ≠ p.2 then Classical.choose (hsep p.1 p.2 h) else 0
  refine ⟨Finset.univ.sup depth, ?_⟩
  intro x y hagree
  by_contra hne
  have hbound : depth (x, y) ≤ Finset.univ.sup depth :=
    Finset.le_sup (Finset.mem_univ (x, y))
  have hd : depth (x, y) = Classical.choose (hsep x y hne) := by
    simp only [depth, dif_pos hne]
  have hdiff := Classical.choose_spec (hsep x y hne)
  apply hdiff
  rw [← hd]
  exact hagree _ hbound

end LinearInputHistorySignature
