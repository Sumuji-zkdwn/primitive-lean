/-!
Quartic classification obtained by composing existing proved certificates.
Provenance: Design's zero-margin equality set and positive-margin uniqueness,
Consequences' arbitrary-input characterization, and GeneralMinimum's two
support equivalences. These are derived results, not new research quotations.
All exact classifications below assume lam > 0. No dynamical conclusion,
uniform positive gap, or conclusion for an arbitrary potential is asserted.
-/
noncomputable section
namespace LinearInputQuarticClassification
open LinearInputDesign LinearInputObservation LinearInputMinimum

/-- At zero margin, the equality certificate is the complete set of actual
full-plane global minimizers. The two reflected points coincide when a = 0. -/
theorem global_minimizer_iff_of_margin_zero {lam r a : ℝ} (hlam : 0 < lam)
    (hmargin : lam * a ^ 2 + r = 0) (x y : ℝ) :
    (∀ z w : ℝ, E lam r (input lam r a) x y ≤ E lam r (input lam r a) z w) ↔
      (x = a ∨ x = -a) ∧ y = Real.sqrt 2 * x := by
  have hmin := globalMin_of_margin (le_of_lt hlam) (le_of_eq hmargin.symm)
  constructor
  · intro h
    exact (equal_energy_iff_of_margin_zero hlam hmargin x y).mp
      (le_antisymm (h a (Real.sqrt 2 * a)) (hmin x y))
  · intro h
    have he := (equal_energy_iff_of_margin_zero hlam hmargin x y).mpr h
    intro z w
    rw [he]
    exact hmin z w

/-- Exact strict-support classification, including the zero-margin quartic
minimum at a = r = 0. The supporting input is forced, not chosen freely. -/
theorem strict_support_iff_input_and_unique_margin {lam r u a : ℝ}
    (hlam : 0 < lam) :
    (∀ x : ℝ, x ≠ a → u * (x - a) <
      (lam * x ^ 4 / 4 + r * x ^ 2 / 2) -
      (lam * a ^ 4 / 4 + r * a ^ 2 / 2)) ↔
    u = input lam r a ∧ (0 < lam * a ^ 2 + r ∨ (a = 0 ∧ r = 0)) := by
  constructor
  · intro hs
    have hscalar := (unique_minimum_iff_strict_support
      (fun t : ℝ => lam * t ^ 4 / 4 + r * t ^ 2 / 2) a u).mpr hs
    have hfull := (quartic_minimum_iff_full lam r u a).mp hscalar.1
    obtain ⟨hu, hm⟩ :=
      (LinearInputConsequences.global_minimum_iff_input_and_margin hlam).mp hfull
    refine ⟨hu, ?_⟩
    rcases eq_or_lt_of_le hm with hz | hp
    · right
      have hmzero : lam * a ^ 2 + r = 0 := hz.symm
      have he := (equal_energy_iff_of_margin_zero hlam hmzero
        (-a) (Real.sqrt 2 * (-a))).mpr ⟨Or.inr rfl, rfl⟩
      have hother : ∀ z : ℝ,
          energy (fun t : ℝ => lam * t ^ 4 / 4 + r * t ^ 2 / 2) id u (-a) ≤
          energy (fun t : ℝ => lam * t ^ 4 / 4 + r * t ^ 2 / 2) id u z := by
        have he' : energy (fun t : ℝ => lam * t ^ 4 / 4 + r * t ^ 2 / 2)
            id u (-a) =
            energy (fun t : ℝ => lam * t ^ 4 / 4 + r * t ^ 2 / 2) id u a := by
          simpa [E, f, energy, hu] using he
        intro z
        rw [he']
        exact hscalar.1 z
      have ha : a = 0 := by linarith [hscalar.2 (-a) hother]
      exact ⟨ha, by simpa [ha] using hmzero⟩
    · exact Or.inl hp
  · rintro ⟨hu, hp | ⟨ha, hr⟩⟩
    · rw [hu]
      exact strict_quartic_support_of_margin_pos (le_of_lt hlam) hp
    · subst a
      subst r
      rw [hu]
      apply (unique_minimum_iff_strict_support
        (fun t : ℝ => lam * t ^ 4 / 4 + 0 * t ^ 2 / 2) 0 (input lam 0 0)).mp
      have hmzero : lam * (0 : ℝ) ^ 2 + 0 = 0 := by ring
      have hmin := (quartic_minimum_iff_full lam 0 (input lam 0 0) 0).mpr
        (globalMin_of_margin (le_of_lt hlam) (le_of_eq hmzero.symm))
      refine ⟨hmin, ?_⟩
      intro x hx
      have he : E lam 0 (input lam 0 0) x (Real.sqrt 2 * x) =
          E lam 0 (input lam 0 0) 0 (Real.sqrt 2 * 0) := by
        simpa [E, f, energy] using le_antisymm (hx 0) (hmin x)
      have heq := (equal_energy_iff_of_margin_zero hlam hmzero
        x (Real.sqrt 2 * x)).mp he
      simpa using heq.1

/-- The strict scalar support criterion classifies unique global minimizers
in the full plane; the nonnegative transverse square forces the valley. -/
theorem unique_global_minimum_iff {lam r u a : ℝ} (hlam : 0 < lam) :
    ((∀ x y : ℝ, E lam r u a (Real.sqrt 2 * a) ≤ E lam r u x y) ∧
      ∀ x y : ℝ, (∀ z w : ℝ, E lam r u x y ≤ E lam r u z w) →
        x = a ∧ y = Real.sqrt 2 * a) ↔
    u = input lam r a ∧ (0 < lam * a ^ 2 + r ∨ (a = 0 ∧ r = 0)) := by
  rw [← strict_support_iff_input_and_unique_margin hlam]
  rw [← unique_minimum_iff_strict_support
    (fun t : ℝ => lam * t ^ 4 / 4 + r * t ^ 2 / 2) a u]
  constructor
  · rintro ⟨hmin, huniq⟩
    refine ⟨(quartic_minimum_iff_full lam r u a).mpr hmin, ?_⟩
    intro x hx
    exact (huniq x (Real.sqrt 2 * x)
      ((quartic_minimum_iff_full lam r u x).mp hx)).1
  · rintro ⟨hmin, huniq⟩
    refine ⟨(quartic_minimum_iff_full lam r u a).mp hmin, ?_⟩
    intro x y hxy
    have hxscalar : ∀ z : ℝ, f lam r u x ≤ f lam r u z := by
      intro z
      have hf : f lam r u x ≤ E lam r u x y :=
        le_add_of_nonneg_right (by positivity)
      exact hf.trans (by simpa [E] using hxy z (Real.sqrt 2 * z))
    have hx : x = a := huniq x hxscalar
    refine ⟨hx, ?_⟩
    subst x
    have he := hxy a (Real.sqrt 2 * a)
    have hs : (y - Real.sqrt 2 * a) ^ 2 ≤ 0 := by
      simp only [E, sub_self, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero] at he
      linarith
    nlinarith [sq_nonneg (y - Real.sqrt 2 * a)]

/-- A supporting input exists uniquely exactly on the realizable target set.
This is uniqueness of input, even where the minimizing point is not unique. -/
theorem existsUnique_support_input_iff {lam r a : ℝ} (hlam : 0 < lam) :
    (∃! u : ℝ, ∀ x : ℝ, u * (x - a) ≤
      (lam * x ^ 4 / 4 + r * x ^ 2 / 2) -
      (lam * a ^ 4 / 4 + r * a ^ 2 / 2)) ↔
    0 ≤ lam * a ^ 2 + r := by
  constructor
  · rintro ⟨u, hu, _⟩
    exact ((quartic_support_iff_input_and_margin hlam).mp hu).2
  · intro hm
    refine ⟨input lam r a,
      (quartic_support_iff_input_and_margin hlam).mpr ⟨rfl, hm⟩, ?_⟩
    intro u hu
    exact ((quartic_support_iff_input_and_margin hlam).mp hu).1

/-- A strict supporting input exists uniquely exactly at the targets admitting
a unique quartic minimum, including the zero-margin origin. -/
theorem existsUnique_strict_support_input_iff {lam r a : ℝ} (hlam : 0 < lam) :
    (∃! u : ℝ, ∀ x : ℝ, x ≠ a → u * (x - a) <
      (lam * x ^ 4 / 4 + r * x ^ 2 / 2) -
      (lam * a ^ 4 / 4 + r * a ^ 2 / 2)) ↔
    0 < lam * a ^ 2 + r ∨ (a = 0 ∧ r = 0) := by
  constructor
  · rintro ⟨u, hu, _⟩
    exact ((strict_support_iff_input_and_unique_margin hlam).mp hu).2
  · intro hm
    refine ⟨input lam r a,
      (strict_support_iff_input_and_unique_margin hlam).mpr ⟨rfl, hm⟩, ?_⟩
    intro u hu
    exact ((strict_support_iff_input_and_unique_margin hlam).mp hu).1

end LinearInputQuarticClassification
