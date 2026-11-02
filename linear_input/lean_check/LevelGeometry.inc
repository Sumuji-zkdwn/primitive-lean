import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Homeomorph.Lemmas

/-!
Geometry of energy levels above the explicit critical-value bound. The radial
inequalities are proved from the actual quartic energy, for arbitrary input u.
-/
noncomputable section
namespace LinearInputLevelGeometry

open LinearInputDesign LinearInputGradient LinearInputGradientBound
open LinearInputCoercivity

theorem radial_gradient_lower_bound {lam : ℝ} (hlam : 0 < lam)
    (r u x y : ℝ) :
    E lam r u x y - (max (-r) 0) ^ 2 / (12 * lam) ≤
      x * gx lam r u x y + y * gy x y := by
  have hi := energy_gradient_identity lam r u x y
  have hb := reduced_energy_bound hlam r x
  have hy : y * gy x y = Real.sqrt 2 * x * gy x y + (gy x y) ^ 2 := by
    unfold gy
    ring
  nlinarith [sq_nonneg (gy x y)]

theorem radial_gradient_pos {lam r u x y : ℝ} (hlam : 0 < lam)
    (he : (max (-r) 0) ^ 2 / (12 * lam) < E lam r u x y) :
    0 < x * gx lam r u x y + y * gy x y := by
  linarith [radial_gradient_lower_bound hlam r u x y]

theorem quadratic_remainder_bound {lam : ℝ} (hlam : 0 < lam)
    (r : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    -3 * lam * q ^ 2 / 4 - r * q / 2 ≤ (max (-r) 0) ^ 2 / (12 * lam) := by
  have h := reduced_energy_bound hlam r (Real.sqrt q)
  have h4 : (Real.sqrt q) ^ 4 = q ^ 2 := by
    rw [show (Real.sqrt q) ^ 4 = ((Real.sqrt q) ^ 2) ^ 2 by ring, Real.sq_sqrt hq]
  simpa only [h4, Real.sq_sqrt hq] using h

/-- Outside the critical-value threshold, outward dilation strictly raises energy. -/
theorem energy_outward_scaling {lam : ℝ} (hlam : 0 < lam)
    (r u x y : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    t * (E lam r u x y - (max (-r) 0) ^ 2 / (12 * lam)) ≤
      E lam r u (t * x) (t * y) - (max (-r) 0) ^ 2 / (12 * lam) := by
  let B := (max (-r) 0) ^ 2 / (12 * lam)
  have hb := quadratic_remainder_bound hlam r (q := t * x ^ 2) (by positivity)
  have hi : E lam r u (t*x) (t*y) - B - t * (E lam r u x y - B) =
      (t - 1) * (B + 3 * lam * (t * x ^ 2) ^ 2 / 4 + r * (t * x ^ 2) / 2 +
        lam * t * (t - 1) ^ 2 * x ^ 4 / 4 + t * (y - Real.sqrt 2 * x) ^ 2 / 2) := by
    unfold E f
    ring
  have hn : 0 ≤ B + 3 * lam * (t * x ^ 2) ^ 2 / 4 + r * (t * x ^ 2) / 2 := by
    change -3 * lam * (t * x ^ 2) ^ 2 / 4 - r * (t * x ^ 2) / 2 ≤ B at hb
    linarith
  have hp : 0 ≤ lam * t * (t - 1) ^ 2 * x ^ 4 / 4 + t * (y - Real.sqrt 2 * x) ^ 2 / 2 := by
    positivity
  have hm := mul_nonneg (sub_nonneg.mpr ht) (add_nonneg hn hp)
  change t * (E lam r u x y - B) ≤ E lam r u (t*x) (t*y) - B
  linarith

theorem energy_outward_strict {lam r u x y t : ℝ} (hlam : 0 < lam)
    (he : (max (-r) 0) ^ 2 / (12 * lam) < E lam r u x y) (ht : 1 < t) :
    E lam r u x y < E lam r u (t*x) (t*y) := by
  have hs := energy_outward_scaling hlam r u x y (le_of_lt ht)
  have hp := mul_pos (sub_pos.mpr ht) (sub_pos.mpr he)
  nlinarith

/-- Each nonzero ray meets each energy level above the threshold exactly once. -/
theorem existsUnique_positive_radius {lam r u e x y : ℝ} (hlam : 0 < lam)
    (he : (max (-r) 0) ^ 2 / (12 * lam) < e) (hz : x ≠ 0 ∨ y ≠ 0) :
    ∃! t : ℝ, 0 < t ∧ E lam r u (t*x) (t*y) = e := by
  have hB : 0 ≤ (max (-r) 0) ^ 2 / (12 * lam) := by positivity
  have he0 : 0 < e := lt_of_le_of_lt hB he
  let q := x ^ 2 + (y - Real.sqrt 2 * x) ^ 2 / 2
  have hq : 0 < q := by
    dsimp [q]
    rcases hz with hx | hy
    · nlinarith [sq_pos_of_ne_zero hx, sq_nonneg (y - Real.sqrt 2 * x)]
    · by_cases hx : x = 0
      · have hysq := sq_pos_of_ne_zero hy
        simpa [hx] using (div_pos hysq (by norm_num : (0 : ℝ) < 2))
      · nlinarith [sq_pos_of_ne_zero hx, sq_nonneg (y - Real.sqrt 2 * x)]
  let T := Real.sqrt ((max (e + lowerBoundConstant lam r u) 0 + 1) / q)
  have hT : 0 < T := Real.sqrt_pos.2 (div_pos (by positivity) hq)
  have hTsq : T ^ 2 * q = max (e + lowerBoundConstant lam r u) 0 + 1 := by
    dsimp [T]
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have hout : e < E lam r u (T*x) (T*y) := by
    have hc := coercive_lower_bound hlam r u (T*x) (T*y)
    have hi : (T*x)^2 + (T*y - Real.sqrt 2*(T*x))^2/2 = T^2*q := by dsimp [q]; ring
    rw [hi, hTsq] at hc
    have hm := le_max_left (e + lowerBoundConstant lam r u) 0
    linarith
  have hcont : Continuous (fun t : ℝ => E lam r u (t*x) (t*y)) := by unfold E f; fun_prop
  have hzE : E lam r u (0*x) (0*y) = 0 := by simp [E, f]
  obtain ⟨t, ht, hte⟩ := intermediate_value_Icc (le_of_lt hT) hcont.continuousOn
    (show e ∈ Set.Icc (E lam r u (0*x) (0*y)) (E lam r u (T*x) (T*y)) by
      rw [hzE]; exact ⟨le_of_lt he0, le_of_lt hout⟩)
  change E lam r u (t*x) (t*y) = e at hte
  have htpos : 0 < t := by
    have htne : t ≠ 0 := by intro h; rw [h, hzE] at hte; linarith
    exact lt_of_le_of_ne ht.1 (Ne.symm htne)
  refine ⟨t, ⟨htpos, hte⟩, ?_⟩
  intro a ha
  rcases lt_trichotomy a t with hat | hat | hat
  · have hratio : 1 < t / a := (lt_div_iff₀ ha.1).2 (by simpa using hat)
    have hh := energy_outward_strict hlam (by rwa [ha.2]) hratio
    have hx : (t/a)*(a*x) = t*x := by field_simp [ne_of_gt ha.1]
    have hy : (t/a)*(a*y) = t*y := by field_simp [ne_of_gt ha.1]
    rw [hx, hy, ha.2, hte] at hh
    exact (lt_irrefl e hh).elim
  · exact hat
  · have hratio : 1 < a / t := (lt_div_iff₀ htpos).2 (by simpa using hat)
    have hh := energy_outward_strict hlam (by rwa [hte]) hratio
    have hx : (a/t)*(t*x) = a*x := by field_simp [ne_of_gt htpos]
    have hy : (a/t)*(t*y) = a*y := by field_simp [ne_of_gt htpos]
    rw [hx, hy, ha.2, hte] at hh
    exact (lt_irrefl e hh).elim

/-- The Euclidean radius is used, rather than the product-space maximum norm. -/
def radius (z : ℝ × ℝ) : ℝ := Real.sqrt (z.1 ^ 2 + z.2 ^ 2)

def direction (z : ℝ × ℝ) : ℝ × ℝ := (z.1 / radius z, z.2 / radius z)

theorem radius_pos {z : ℝ × ℝ} (hz : z.1 ≠ 0 ∨ z.2 ≠ 0) : 0 < radius z := by
  apply Real.sqrt_pos.2
  rcases hz with h | h
  · nlinarith [sq_pos_of_ne_zero h, sq_nonneg z.2]
  · nlinarith [sq_pos_of_ne_zero h, sq_nonneg z.1]

theorem radius_pos_of_energy {lam r u : ℝ} (hlam : 0 < lam) {z : ℝ × ℝ}
    (he : (max (-r) 0) ^ 2 / (12 * lam) < E lam r u z.1 z.2) : 0 < radius z := by
  apply radius_pos
  by_contra hz
  push Not at hz
  have hB : 0 ≤ (max (-r) 0) ^ 2 / (12 * lam) := by positivity
  simp [hz.1, hz.2, E, f] at he
  linarith

theorem direction_mem_circle {z : ℝ × ℝ} (hz : 0 < radius z) :
    (direction z).1 ^ 2 + (direction z).2 ^ 2 = 1 := by
  have hs : radius z ^ 2 = z.1 ^ 2 + z.2 ^ 2 := Real.sq_sqrt (by positivity)
  dsimp [direction]
  field_simp [ne_of_gt hz]
  exact hs.symm

theorem radius_mul_direction {z : ℝ × ℝ} (hz : 0 < radius z) :
    (radius z * (direction z).1, radius z * (direction z).2) = z := by
  apply Prod.ext <;> dsimp [direction] <;> field_simp [ne_of_gt hz]

theorem direction_positive_scale (z : ℝ × ℝ) {t : ℝ} (ht : 0 < t) :
    direction (t*z.1, t*z.2) = direction z := by
  have hr : radius (t*z.1, t*z.2) = t * radius z := by
    dsimp [radius]
    rw [show (t*z.1)^2+(t*z.2)^2 = t^2*(z.1^2+z.2^2) by ring,
      Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq (le_of_lt ht)]
  apply Prod.ext <;> dsimp only [direction, Prod.fst, Prod.snd] <;>
    rw [hr] <;> exact mul_div_mul_left _ _ (ne_of_gt ht)

theorem direction_of_circle {v : ℝ × ℝ} (hv : v.1 ^ 2 + v.2 ^ 2 = 1) :
    direction v = v := by
  simp [direction, radius, hv]

theorem continuous_radius : Continuous radius := by unfold radius; fun_prop

theorem continuous_direction_subtype {S : Set (ℝ × ℝ)}
    (hS : ∀ z : S, 0 < radius z.val) : Continuous (fun z : S => direction z.val) := by
  apply Continuous.prodMk
  · exact (continuous_fst.comp continuous_subtype_val).div
      (continuous_radius.comp continuous_subtype_val) (fun z => ne_of_gt (hS z))
  · exact (continuous_snd.comp continuous_subtype_val).div
      (continuous_radius.comp continuous_subtype_val) (fun z => ne_of_gt (hS z))

/-- Direction and energy determine a point uniquely above the threshold. -/
theorem eq_of_direction_energy_eq {lam r u : ℝ} (hlam : 0 < lam) {z w : ℝ × ℝ}
    (he : (max (-r) 0) ^ 2 / (12 * lam) < E lam r u z.1 z.2)
    (hd : direction z = direction w) (hE : E lam r u z.1 z.2 = E lam r u w.1 w.2) :
    z = w := by
  have hz := radius_pos_of_energy hlam he
  have hw := radius_pos_of_energy hlam (he.trans_eq hE)
  have hx : z.1 * radius w = w.1 * radius z :=
    (div_eq_div_iff (ne_of_gt hz) (ne_of_gt hw)).1 (congrArg Prod.fst hd)
  have hy : z.2 * radius w = w.2 * radius z :=
    (div_eq_div_iff (ne_of_gt hz) (ne_of_gt hw)).1 (congrArg Prod.snd hd)
  have hscaleW : (radius w / radius z * z.1, radius w / radius z * z.2) = w := by
    apply Prod.ext
    · dsimp only
      rw [div_mul_eq_mul_div]
      apply (div_eq_iff (ne_of_gt hz)).2
      nlinarith
    · dsimp only
      rw [div_mul_eq_mul_div]
      apply (div_eq_iff (ne_of_gt hz)).2
      nlinarith
  have hscaleZ : (radius z / radius w * w.1, radius z / radius w * w.2) = z := by
    apply Prod.ext
    · dsimp only
      rw [div_mul_eq_mul_div]
      apply (div_eq_iff (ne_of_gt hw)).2
      nlinarith
    · dsimp only
      rw [div_mul_eq_mul_div]
      apply (div_eq_iff (ne_of_gt hw)).2
      nlinarith
  rcases lt_trichotomy (radius z) (radius w) with hlt | heq | hlt
  · have hs := energy_outward_strict hlam he
      ((lt_div_iff₀ hz).2 (by simpa using hlt))
    have hws := congrArg (fun q : ℝ × ℝ => E lam r u q.1 q.2) hscaleW
    change E lam r u (radius w / radius z * z.1) (radius w / radius z * z.2) =
      E lam r u w.1 w.2 at hws
    linarith
  · apply Prod.ext
    · exact (mul_right_cancel₀ (ne_of_gt hw)) (by simpa only [heq] using hx)
    · exact (mul_right_cancel₀ (ne_of_gt hw)) (by simpa only [heq] using hy)
  · have hs := energy_outward_strict hlam (he.trans_eq hE)
      ((lt_div_iff₀ hw).2 (by simpa using hlt))
    have hzs := congrArg (fun q : ℝ × ℝ => E lam r u q.1 q.2) hscaleZ
    change E lam r u (radius z / radius w * w.1) (radius z / radius w * w.2) =
      E lam r u z.1 z.2 at hzs
    linarith

/-- The actual high energy level is homeomorphic to the Euclidean unit circle. -/
def levelHomeomorphCircle {lam : ℝ} (hlam : 0 < lam) (r u e : ℝ)
    (he : (max (-r) 0) ^ 2 / (12 * lam) < e) :
    {z : ℝ × ℝ // E lam r u z.1 z.2 = e} ≃ₜ
      {v : ℝ × ℝ // v.1 ^ 2 + v.2 ^ 2 = 1} := by
  let L := {z : ℝ × ℝ | E lam r u z.1 z.2 = e}
  have hpos (z : L) : 0 < radius z.val :=
    radius_pos_of_energy hlam (by rw [z.property]; exact he)
  let F : L → {v : ℝ × ℝ // v.1 ^ 2 + v.2 ^ 2 = 1} :=
    fun z => ⟨direction z.val, direction_mem_circle (hpos z)⟩
  have hcont : Continuous F := (continuous_direction_subtype hpos).subtype_mk _
  have hinj : Function.Injective F := by
    intro z w h
    apply Subtype.ext
    apply eq_of_direction_energy_eq hlam (by rw [z.property]; exact he)
    · exact congrArg Subtype.val h
    · exact z.property.trans w.property.symm
  have hsurj : Function.Surjective F := by
    intro v
    have hv : v.val.1 ≠ 0 ∨ v.val.2 ≠ 0 := by
      by_contra h
      push Not at h
      have hc := v.property
      simp [h.1, h.2] at hc
    obtain ⟨t, ht, _⟩ := existsUnique_positive_radius hlam he hv
    refine ⟨⟨(t*v.val.1, t*v.val.2), ht.2⟩, ?_⟩
    apply Subtype.ext
    change direction (t*v.val.1, t*v.val.2) = v.val
    rw [direction_positive_scale _ ht.1, direction_of_circle v.property]
  have hc : IsCompact L := (isCompact_sublevel hlam r u e).of_isClosed_subset
    (isClosed_eq (continuous_energy lam r u) continuous_const) (fun _ hz => le_of_eq hz)
  letI : CompactSpace {z : ℝ × ℝ // E lam r u z.1 z.2 = e} :=
    isCompact_iff_compactSpace.mp hc
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F ⟨hinj, hsurj⟩) hcont

/-- A closed high-energy band is the product of the Euclidean circle and its
energy interval. If lo < hi, this is a closed topological annulus. -/
def bandHomeomorphCylinder {lam : ℝ} (hlam : 0 < lam) (r u lo hi : ℝ)
    (hlo : (max (-r) 0) ^ 2 / (12 * lam) < lo) :
    {z : ℝ × ℝ // lo ≤ E lam r u z.1 z.2 ∧ E lam r u z.1 z.2 ≤ hi} ≃ₜ
      ({v : ℝ × ℝ // v.1 ^ 2 + v.2 ^ 2 = 1} × Set.Icc lo hi) := by
  let K := {z : ℝ × ℝ | lo ≤ E lam r u z.1 z.2 ∧ E lam r u z.1 z.2 ≤ hi}
  have hpos (z : K) : 0 < radius z.val :=
    radius_pos_of_energy hlam (lt_of_lt_of_le hlo z.property.1)
  let F : K → ({v : ℝ × ℝ // v.1 ^ 2 + v.2 ^ 2 = 1} × Set.Icc lo hi) :=
    fun z => (⟨direction z.val, direction_mem_circle (hpos z)⟩,
      ⟨E lam r u z.val.1 z.val.2, z.property⟩)
  have hcont : Continuous F :=
    ((continuous_direction_subtype hpos).subtype_mk _).prodMk
      (((continuous_energy lam r u).comp continuous_subtype_val).subtype_mk _)
  have hinj : Function.Injective F := by
    intro z w h
    apply Subtype.ext
    apply eq_of_direction_energy_eq hlam (lt_of_lt_of_le hlo z.property.1)
    · exact congrArg (fun q => q.1.val) h
    · exact congrArg (fun q => q.2.val) h
  have hsurj : Function.Surjective F := by
    intro v
    have hv : v.1.val.1 ≠ 0 ∨ v.1.val.2 ≠ 0 := by
      by_contra h
      push Not at h
      have hc := v.1.property
      simp [h.1, h.2] at hc
    obtain ⟨t, ht, _⟩ := existsUnique_positive_radius hlam
      (lt_of_lt_of_le hlo v.2.property.1) hv
    have hmem : (t*v.1.val.1, t*v.1.val.2) ∈ K := by
      change lo ≤ E lam r u (t*v.1.val.1) (t*v.1.val.2) ∧
        E lam r u (t*v.1.val.1) (t*v.1.val.2) ≤ hi
      rw [ht.2]
      exact v.2.property
    refine ⟨⟨(t*v.1.val.1, t*v.1.val.2), hmem⟩, ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      change direction (t*v.1.val.1, t*v.1.val.2) = v.1.val
      rw [direction_positive_scale _ ht.1, direction_of_circle v.1.property]
    · apply Subtype.ext
      exact ht.2
  letI : CompactSpace {z : ℝ × ℝ // lo ≤ E lam r u z.1 z.2 ∧ E lam r u z.1 z.2 ≤ hi} :=
    isCompact_iff_compactSpace.mp (isCompact_band hlam r u lo hi)
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F ⟨hinj, hsurj⟩) hcont

end LinearInputLevelGeometry
