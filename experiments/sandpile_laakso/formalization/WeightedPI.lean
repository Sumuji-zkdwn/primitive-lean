import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Tactic

/-!
Real-exponent WFS weights on a ball and on the central cut.

The central half-band is parametrized by x = |2t-1|, 0 ≤ x ≤ δ.
The two halves together have Lebesgue measure dx in this coordinate.
The upper gradient of a unit ramp in weighted length is constant on
the band. Its weighted integral is therefore the ratio of the two
power integrals below. All exponents in this file are real.

The ball transfer uses a base measure, actual set integrals, and the
unweighted PI on a comparison ball. Ball inclusions, the radius
comparison, and the interpretation of the test functions on the
Laakso quotient are geometric inputs (see fixed_gate_pi.md).
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace SubLaakso.WFS

def bandVolume (p δ : ℝ) : ℝ := ∫ x in (0 : ℝ)..δ, x ^ p

theorem bandVolume_eq {p : ℝ} (hp : 0 ≤ p) (δ : ℝ) :
    bandVolume p δ = δ ^ (p + 1) / (p + 1) := by
  unfold bandVolume
  rw [integral_rpow (.inl (by linarith)), Real.zero_rpow (by linarith), sub_zero]

/-- On any oriented interval the calibrated density has exactly the
length of its signed-power image. For u ≤ v the interval integral is
the mass on (u,v]; these intervals determine the Borel measure. The
displayed endpoint formula unfolds to ObservedSandpile.signedPower. -/
theorem calibrated_interval_mass {a : ℝ} (ha : 0 ≤ a) (u v : ℝ) :
    (∫ x in u..v, (a+1)*|x|^a) =
      (if 0 ≤ v then v^(a+1) else -((-v)^(a+1))) -
      (if 0 ≤ u then u^(a+1) else -((-u)^(a+1))) := by
  let F := fun x : ℝ => if 0 ≤ x then x^(a+1) else -((-x)^(a+1))
  have poscase (x : ℝ) (hx : 0 ≤ x) : (∫ y in 0..x, |y|^a) = x^(a+1)/(a+1) := by
    apply Eq.trans _ (bandVolume_eq ha x)
    apply intervalIntegral.integral_congr
    intro y hy
    have hy' : 0 ≤ y := (uIcc_of_le hx ▸ hy).1
    change |y|^a = y^a
    rw [abs_of_nonneg hy']
  have primitive (x : ℝ) : (∫ y in 0..x, |y|^a) = F x/(a+1) := by
    by_cases hx : 0 ≤ x
    · simpa [F,hx] using poscase x hx
    · have hs := intervalIntegral.integral_comp_neg (a := 0) (b := x) (fun y : ℝ => |y|^a)
      simp only [abs_neg, neg_zero] at hs
      rw [hs, intervalIntegral.integral_symm, poscase (-x) (by linarith)]
      simp [F,hx,neg_div]
  have hc : Continuous (fun y : ℝ => |y|^a) := (Real.continuous_rpow_const ha).comp continuous_abs
  have add : (∫ y in (0:ℝ)..u, |y|^a) + (∫ y in u..v, |y|^a) = ∫ y in (0:ℝ)..v, |y|^a :=
    intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 u) (hc.intervalIntegrable u v)
  rw [primitive u, primitive v] at add
  have hadd : (∫ y in u..v, |y|^a) = F v/(a+1)-F u/(a+1) := by linarith
  rw [intervalIntegral.integral_const_mul, hadd]
  change (a+1) * (F v/(a+1)-F u/(a+1)) = F v-F u
  have h : 0 < a+1 := by linarith
  field_simp

def rampEnergy (a b δ : ℝ) : ℝ := bandVolume a δ / bandVolume b δ

theorem rampEnergy_eq {a b δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 < δ) :
    rampEnergy a b δ = ((b + 1) / (a + 1)) * δ ^ (a-b) := by
  rw [rampEnergy, bandVolume_eq ha, bandVolume_eq hb,
    show a-b = (a+1)-(b+1) by ring, Real.rpow_sub hd]
  field_simp

theorem rampEnergy_tendsto_zero {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hlt : b < a) :
    Tendsto (rampEnergy a b) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hp : 0 < a-b := sub_pos.mpr hlt
  have hcont := (Real.continuous_rpow_const hp.le).continuousAt (x := (0:ℝ))
  have ht : Tendsto (fun x : ℝ => x ^ (a-b)) (𝓝[>] 0) (𝓝 0) := by
    simpa [ContinuousWithinAt, Real.zero_rpow hp.ne'] using hcont.continuousWithinAt (s := Ioi (0:ℝ))
  have hc := ht.const_mul ((b+1)/(a+1))
  apply ((show Tendsto (fun x : ℝ => (b+1)/(a+1) * x ^ (a-b)) (𝓝[>] 0) (𝓝 0) by
    simpa using hc)).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (rampEnergy_eq ha hb hx).symm

/-- A uniform positive lower bound on the energies of all narrow central
ramps is equivalent to the sharp order of the exponents. -/
theorem uniform_ramp_energy_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∃ c : ℝ, 0 < c ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 → c ≤ rampEnergy a b δ) ↔ a ≤ b := by
  constructor
  · rintro ⟨c, hc, h⟩
    by_contra! hlt
    have hev : ∀ᶠ δ : ℝ in 𝓝[>] 0, c ≤ rampEnergy a b δ := by
      have half : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ≤ 1/2 :=
        (eventually_le_nhds (by norm_num : (0:ℝ) < 1/2)).filter_mono nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin, half] with δ hδ hδ'
      exact h δ hδ hδ'
    exact (not_le.mpr hc) (le_of_tendsto_of_tendsto tendsto_const_nhds
      (rampEnergy_tendsto_zero ha hb hlt) hev)
  · intro hab
    have hK : 0 < (b+1)/(a+1) := by positivity
    refine ⟨_, hK, ?_⟩
    intro δ hδ hδ'
    rw [rampEnergy_eq ha hb hδ]
    exact le_mul_of_one_le_right hK.le
      (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ (by linarith) (by linarith))

/-- Mean absolute oscillation of the symmetric ramp. On each half its
distance to 1/2 is (x/δ)^(b+1)/2 for x ≤ δ and 1/2 for x ≥ δ. -/
def rampOsc (a b δ : ℝ) : ℝ :=
  ((∫ x in δ..1, x ^ a) + bandVolume (a+b+1) δ / δ^(b+1)) / (2 * bandVolume a 1)

theorem rampOsc_eq {a b δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 < δ) :
    rampOsc a b δ = (1 - (b+1)/(a+b+2)*δ^(a+1))/2 := by
  rw [rampOsc, integral_rpow (.inl (by linarith)), Real.one_rpow,
    bandVolume_eq (p := a+b+1) (by linarith), bandVolume_eq ha, Real.one_rpow,
    show a+b+1+1 = (a+1)+(b+1) by ring, Real.rpow_add hd (a+1) (b+1)]
  have h1 : 0 < a+1 := by linarith
  have h2 : 0 < a+b+2 := by linarith
  have h3 : 0 < (a+1)+(b+1) := by linarith
  have h4 := Real.rpow_pos_of_pos hd (b+1)
  field_simp
  ring

theorem rampOsc_tendsto_half {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Tendsto (rampOsc a b) (𝓝[>] (0:ℝ)) (𝓝 (1/2)) := by
  have hp : 0 < a+1 := by linarith
  have hcont := (Real.continuous_rpow_const hp.le).continuousAt (x := (0:ℝ))
  have ht : Tendsto (fun x : ℝ => x ^ (a+1)) (𝓝[>] 0) (𝓝 0) := by
    simpa [ContinuousWithinAt, Real.zero_rpow hp.ne'] using hcont.continuousWithinAt (s := Ioi (0:ℝ))
  have hf : Tendsto (fun x : ℝ => (1 - (b+1)/(a+b+2)*x^(a+1))/2) (𝓝[>] 0) (𝓝 (1/2)) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub (ht.const_mul ((b+1)/(a+b+2))) |>.div_const 2
  apply hf.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (rampOsc_eq ha hb hx).symm

/-- Uniform PI inequality restricted to the actual central-ramp integrals. -/
theorem ramp_test_PI_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 →
      rampOsc a b δ ≤ C * rampEnergy a b δ) ↔ a ≤ b := by
  constructor
  · rintro ⟨C, _, hC⟩
    by_contra! hlt
    have hev : ∀ᶠ δ : ℝ in 𝓝[>] 0, rampOsc a b δ ≤ C * rampEnergy a b δ := by
      have half : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ≤ 1/2 :=
        (eventually_le_nhds (by norm_num : (0:ℝ) < 1/2)).filter_mono nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin, half] with δ hδ hδ'
      exact hC δ hδ hδ'
    have hc := le_of_tendsto_of_tendsto (rampOsc_tendsto_half ha hb)
      ((rampEnergy_tendsto_zero ha hb hlt).const_mul C) hev
    norm_num at hc
  · intro hab
    obtain ⟨k, hk, henergy⟩ := (uniform_ramp_energy_iff ha hb).2 hab
    refine ⟨k⁻¹, inv_pos.mpr hk, ?_⟩
    intro δ hd hhalf
    have hE := mul_le_mul_of_nonneg_left (henergy δ hd hhalf) (inv_pos.mpr hk).le
    rw [inv_mul_cancel₀ hk.ne'] at hE
    apply le_trans _ hE
    rw [rampOsc_eq ha hb hd]
    have : 0 ≤ (b+1)/(a+b+2)*δ^(a+1) := by positivity
    linarith

/-- Local pointwise inequality on the expanded comparison ball. -/
theorem compare_powers {x H a b : ℝ} (hx : 0 ≤ x) (hxH : x ≤ H)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    x ^ b ≤ H ^ (b-a) * x ^ a := by
  have he : 0 ≤ b-a := sub_nonneg.mpr hab
  calc
    x ^ b = x ^ (b-a) * x ^ a := by
      rw [← Real.rpow_add_of_nonneg hx he ha]
      congr 1
      ring
    _ ≤ H ^ (b-a) * x ^ a := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hx hxH he) (Real.rpow_nonneg hx _)

/-- At least one quarter of any interval is uniformly far from the
singular height, simultaneously relative to its length and starting
height t. Coordinates are translated so the singular height is zero. -/
theorem outer_quarter {u v t : ℝ} (htu : u ≤ t) (htv : t ≤ v) :
    ∃ p q : ℝ, u ≤ p ∧ p ≤ q ∧ q ≤ v ∧ q-p = (v-u)/4 ∧
      ∀ z ∈ Icc p q, (|t|+(v-u))/6 ≤ |z| := by
  rcases le_total 0 (u+v) with h | h
  · refine ⟨v-(v-u)/4, v, by linarith, by linarith, le_rfl, by ring, ?_⟩
    intro z hz
    have hs : |t| ≤ v := abs_le.mpr ⟨by linarith, htv⟩
    have hz' := hz.1
    have := le_abs_self z
    linarith
  · refine ⟨u, u+(v-u)/4, le_rfl, by linarith, by linarith, by ring, ?_⟩
    intro z hz
    have hs : |t| ≤ -u := abs_le.mpr ⟨by linarith, by linarith⟩
    have hz' := hz.2
    have := neg_le_abs z
    linarith

theorem interval_sweep_lower {u v t b : ℝ} (htu : u ≤ t) (htv : t ≤ v) (hb : 0 ≤ b) :
    (v-u)/4 * ((|t|+(v-u))/6)^b ≤ ∫ x in u..v, |x|^b := by
  obtain ⟨p,q,hup,hpq,hqv,hlen,hfar⟩ := outer_quarter htu htv
  have hcont := (Real.continuous_rpow_const hb).comp continuous_abs
  have hbase : 0 ≤ (|t|+(v-u))/6 := by linarith [abs_nonneg t]
  calc
    _ = ∫ _ in p..q, ((|t|+(v-u))/6)^b := by
      rw [intervalIntegral.integral_const, hlen, smul_eq_mul]
    _ ≤ ∫ x in p..q, |x|^b := intervalIntegral.integral_mono_on hpq
      intervalIntegrable_const (hcont.intervalIntegrable _ _)
      (fun z hz => Real.rpow_le_rpow hbase (hfar z hz) hb)
    _ ≤ _ := intervalIntegral.integral_mono_interval hup hpq hqv
      (ae_of_all _ fun z => Real.rpow_nonneg (abs_nonneg z) _) (hcont.intervalIntegrable _ _)

/-- Metric estimate from the two geometric path facts on the quotient.
Each path traverses its entire height footprint and can be replaced in
the raw distance by at most three height sweeps. One raw shortest path
gives the upper bound. Here h=|t| after shifting the central height;
returning to |2t-1| multiplies all weighted lengths by 2^b. -/
theorem weighted_path_distance_bounds {Path : Type*}
    (cost lo hi : Path → ℝ) (t r b : ℝ) (hr : 0 ≤ r) (hb : 0 ≤ b)
    (start : ∀ p, lo p ≤ t ∧ t ≤ hi p)
    (sweep : ∀ p, r ≤ 3 * (hi p - lo p))
    (traverse : ∀ p, (∫ z in lo p..hi p, |z|^b) ≤ cost p)
    (short : ∃ p, cost p ≤ r*(|t|+r)^b) :
    r/12 * ((|t|+r)/18)^b ≤ sInf (range cost) ∧
      sInf (range cost) ≤ r*(|t|+r)^b := by
  obtain ⟨p₀, hp₀⟩ := short
  have bound (p : Path) : r/12 * ((|t|+r)/18)^b ≤ cost p := by
    obtain ⟨ht₁, ht₂⟩ := start p
    have hs := sweep p
    have h₁ : r/12 ≤ (hi p - lo p)/4 := by linarith
    have h₂ : (|t|+r)/18 ≤ (|t|+(hi p-lo p))/6 := by linarith [abs_nonneg t]
    have h₃ : 0 ≤ (|t|+r)/18 := by positivity
    exact (mul_le_mul h₁ (Real.rpow_le_rpow h₃ h₂ hb)
      (Real.rpow_nonneg h₃ _) (by linarith)).trans
      ((interval_sweep_lower ht₁ ht₂ hb).trans (traverse p))
  have lb : r/12 * ((|t|+r)/18)^b ∈ lowerBounds (range cost) := by
    rintro _ ⟨p,rfl⟩; exact bound p
  exact ⟨le_csInf ⟨cost p₀, p₀, rfl⟩ lb, (csInf_le ⟨_, lb⟩ (mem_range_self p₀)).trans hp₀⟩

section Transfer
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {B U V W : Set X} {h f g : X → ℝ}

def mass (μ : Measure X) (w : X → ℝ) (B : Set X) : ℝ := ∫ x in B, w x ∂μ
def mean (μ : Measure X) (w f : X → ℝ) (B : Set X) : ℝ :=
  (∫ x in B, w x * f x ∂μ) / mass μ w B

def deviation (μ : Measure X) (w f : X → ℝ) (B : Set X) (c : ℝ) : ℝ :=
  ∫ x in B, w x * |f x - c| ∂μ

theorem deviation_le_twice {w : X → ℝ} (hw : ∀ x, 0 ≤ w x)
    (hm : 0 < mass μ w B) (hiw : IntegrableOn w B μ)
    (hif : IntegrableOn (fun x => w x * f x) B μ) (c : ℝ) :
    deviation μ w f B (mean μ w f B) ≤ 2 * deviation μ w f B c := by
  let m := mean μ w f B
  have repr (z : ℝ) : (fun x => w x * (f x - z)) =
      (fun x => w x * f x) - (fun x => w x * z) := by
    funext x; simp [mul_sub]
  have dint (z : ℝ) : IntegrableOn (fun x => w x * (f x - z)) B μ := by
    rw [repr]; exact hif.sub (hiw.mul_const _)
  have abs_repr (z : ℝ) : (fun x => w x * |f x-z|) =
      (fun x => ‖w x * (f x-z)‖) := by
    funext x; simp [Real.norm_eq_abs, abs_of_nonneg (hw x)]
  have absint (z : ℝ) : IntegrableOn (fun x => w x * |f x-z|) B μ := by
    rw [abs_repr]; exact (dint z).norm
  have idiff : (∫ x in B, w x * (f x-c) ∂μ) = mass μ w B * (m-c) := by
    simp_rw [mul_sub]
    rw [integral_sub hif (hiw.mul_const c), integral_mul_const]
    change (∫ x in B, w x * f x ∂μ) - mass μ w B * c =
      mass μ w B * ((∫ x in B, w x * f x ∂μ) / mass μ w B) - mass μ w B * c
    field_simp
  have hj : mass μ w B * |m-c| ≤ deviation μ w f B c := by
    have hj' := norm_integral_le_integral_norm (μ := μ.restrict B) (fun x => w x * (f x-c))
    rw [← abs_repr, idiff, Real.norm_eq_abs, abs_mul, abs_of_pos hm] at hj'
    exact hj'
  calc
    deviation μ w f B m ≤ ∫ x in B, (w x * |f x - c| + w x * |m - c|) ∂μ := by
      apply integral_mono (absint m) ((absint c).add (hiw.mul_const _))
      intro x
      change w x * |f x - m| ≤ w x * |f x - c| + w x * |m-c|
      rw [← mul_add]
      apply mul_le_mul_of_nonneg_left _ (hw x)
      simpa [abs_sub_comm c m] using abs_sub_le (f x) c m
    _ = deviation μ w f B c + mass μ w B * |m-c| := by
      rw [integral_add (absint c) (hiw.mul_const _), integral_mul_const]; rfl
    _ ≤ 2 * deviation μ w f B c := by linarith

/-- Transfer one ball of a base PI to the new measure and length. B is
the weighted ball, U the enclosing unweighted ball, V its unweighted
dilation and W the enclosing weighted dilation. The base PI is stated
with an arbitrary admissible centering constant c (typically its mean). -/
theorem transfer_ball {a b H r K c : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hr : 0 ≤ r) (hK : 0 ≤ K) (hH : 0 < H)
    (hh : ∀ x, 0 ≤ h x) (hg : ∀ x, 0 ≤ g x)
    (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hBU : B ⊆ U) (hVW : V ⊆ W)
    (hu : ∀ x ∈ U, h x ≤ H) (hv : ∀ x ∈ V, h x ≤ H)
    (hw : IntegrableOn (fun x => h x ^ a) B μ)
    (hwf : IntegrableOn (fun x => h x ^ a * f x) B μ)
    (hm : 0 < mass μ (fun x => h x ^ a) B)
    (hdev : IntegrableOn (fun x => h x ^ a * |f x-c|) U μ)
    (hbase : IntegrableOn (fun x => |f x-c|) U μ)
    (hbg : IntegrableOn (fun x => h x ^ b * g x) V μ)
    (hag : IntegrableOn (fun x => h x ^ a * g x) W μ)
    (basePI : (∫ x in U, |f x-c| ∂μ) ≤ K*r * ∫ x in V, h x ^ b * g x ∂μ) :
    deviation μ (fun x => h x ^ a) f B (mean μ (fun x => h x ^ a) f B) ≤
      (2*K) * (r * H^b) * ∫ x in W, h x ^ a * g x ∂μ := by
  let w := fun x => h x ^ a
  have wpos : ∀ x, 0 ≤ w x := fun x => Real.rpow_nonneg (hh x) _
  have hA := Real.rpow_nonneg hH.le a
  have hD := Real.rpow_nonneg hH.le (b-a)
  have devle : deviation μ w f B c ≤ H^a * ∫ x in U, |f x-c| ∂μ := calc
    _ ≤ ∫ x in U, w x * |f x-c| ∂μ := setIntegral_mono_set hdev
      (ae_of_all _ fun x => mul_nonneg (wpos x) (abs_nonneg _)) hBU.eventuallyLE
    _ ≤ ∫ x in U, H^a * |f x-c| ∂μ := by
      apply setIntegral_mono_on hdev (hbase.const_mul _) hU
      intro x hx
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (hh x) (hu x hx) ha) (abs_nonneg _)
    _ = _ := integral_const_mul _ _
  have gradle : (∫ x in V, h x ^ b * g x ∂μ) ≤ H^(b-a) * ∫ x in W, w x * g x ∂μ := calc
    _ ≤ ∫ x in V, H^(b-a) * (w x * g x) ∂μ := by
      apply setIntegral_mono_on hbg ((hag.mono_set hVW).const_mul _) hV
      intro x hx
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right
        (compare_powers (hh x) (hv x hx) ha hab) (hg x)
    _ = H^(b-a) * ∫ x in V, w x * g x ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (setIntegral_mono_set hag
      (ae_of_all _ fun x => mul_nonneg (wpos x) (hg x)) hVW.eventuallyLE) hD
  have combine : H^a * H^(b-a) = H^b := by
    rw [← Real.rpow_add hH]; congr 1; ring
  calc
    _ ≤ 2 * deviation μ w f B c := deviation_le_twice wpos hm hw hwf c
    _ ≤ 2 * (H^a * (K*r * (H^(b-a) * ∫ x in W, w x * g x ∂μ))) := by
      gcongr
      exact devle.trans (mul_le_mul_of_nonneg_left
        (basePI.trans (mul_le_mul_of_nonneg_left gradle (mul_nonneg hK hr))) hA)
    _ = _ := by dsimp [w]; rw [← combine]; ring

end Transfer

/-- The step from an integral PI to a normalized PI uses precisely an
upper bound on the mass growth to the dilated ball. -/
theorem normalize_PI {A I m M C R D : ℝ}
    (hm : 0 < m) (hM : 0 < M) (hI : 0 ≤ I) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (integralPI : A ≤ C*R*I) (massGrowth : M ≤ D*m) :
    A/m ≤ (D*C)*R*(I/M) := by
  apply (div_le_iff₀ hm).2
  apply integralPI.trans
  calc
    C*R*I = (C*R*I*M)/M := by field_simp
    _ ≤ (C*R*I*(D*m))/M := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left massGrowth (mul_nonneg (mul_nonneg hC hR) hI)) hM.le
    _ = _ := by ring

/-- Equality of the central and off-centre volume exponents is exactly
the calibration a=bQ. -/
theorem equal_dimensions_iff {Q a b : ℝ} (hb : 0 ≤ b) :
    (Q+a)/(1+b) = Q ↔ a = b*Q := by
  rw [div_eq_iff (show (1+b : ℝ) ≠ 0 by positivity)]
  constructor <;> intro h <;> nlinarith

/-- Under that calibration the entire ball-mass profile, not just its
central exponent, is exactly the Q-th power of the radius profile. -/
theorem calibrated_ball_profile {Q a b r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hcal : a = b*Q) :
    (s+r)^a * r^Q = (r*(s+r)^b)^Q := by
  rw [Real.mul_rpow hr (Real.rpow_nonneg (add_nonneg hs hr) _),
    ← Real.rpow_mul (add_nonneg hs hr), hcal]
  ring

/-- For Q>1, a calibrated globally regular model with fixed gates has
the PI exponent order precisely in the unweighted case. -/
theorem equal_dimensions_and_PI_order_iff {Q a b : ℝ} (hQ : 1 < Q)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((Q+a)/(1+b) = Q ∧ a ≤ b) ↔ (a = 0 ∧ b = 0) := by
  rw [equal_dimensions_iff hb]
  constructor
  · rintro ⟨hcal, hab⟩
    have hzero : b = 0 := by
      by_contra h
      have hlt := mul_lt_mul_of_pos_left hQ (lt_of_le_of_ne hb (Ne.symm h))
      nlinarith
    exact ⟨le_antisymm (hab.trans hzero.le) ha, hzero⟩
  · rintro ⟨rfl,rfl⟩
    simp

#print axioms bandVolume_eq
#print axioms calibrated_interval_mass
#print axioms ramp_test_PI_iff
#print axioms interval_sweep_lower
#print axioms weighted_path_distance_bounds
#print axioms transfer_ball
#print axioms normalize_PI
#print axioms equal_dimensions_and_PI_order_iff

end SubLaakso.WFS
