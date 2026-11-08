import Research.SphereClockWordNormalForm

/-!
# Sphere clock: exact endpoint observability

This module derives the necessary-and-sufficient test for equality of
two operation-word endpoints from the *existing* Glued quotient and
wordAction normal form. No Elastica or SphereClock definitions are changed.

A single initial point at a gluing angle loses the flip parity; outside
H, the total rotation and parity are both observable. When H is proper,
the entire action on ClockSpace distinguishes all normal forms.

All statements concern abstract quotient maps, not physical rotations,
holonomy, or quantum effects.
-/

namespace SphereClock.RationalGluing

section Abstract

variable {G : Type*} [AddCommGroup G]

/-- Equality of represented points is exactly the original gluing relation. -/
theorem point_eq_iff_glued (H : AddSubgroup G)
    (θ φ : G) (b c : Bool) :
    point H θ b = point H φ c ↔
      θ = φ ∧ (b = c ∨ θ ∈ H) := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

/-- Unfold a rotation followed by an optional layer flip at a point. -/
theorem normal_form_at_point (H : AddSubgroup G)
    (δ : H) (odd : Bool) (θ : G) (b : Bool) :
    (if odd then
      flipSpace H (rotateSpace H (δ : G) δ.property (point H θ b))
    else
      rotateSpace H (δ : G) δ.property (point H θ b)) =
      point H (θ + (δ : G)) (if odd then !b else b) := by
  cases odd <;> rfl

/-- Exact test for equality of two normal forms at one starting point. -/
theorem normal_forms_point_eq_iff (H : AddSubgroup G)
    (δ ε : H) (odd other : Bool) (θ : G) (b : Bool) :
    (if odd then
      flipSpace H (rotateSpace H (δ : G) δ.property (point H θ b))
    else
      rotateSpace H (δ : G) δ.property (point H θ b)) =
    (if other then
      flipSpace H (rotateSpace H (ε : G) ε.property (point H θ b))
    else
      rotateSpace H (ε : G) ε.property (point H θ b)) ↔
      δ = ε ∧ (odd = other ∨ θ ∈ H) := by
  rw [normal_form_at_point H δ odd θ b,
      normal_form_at_point H ε other θ b,
      point_eq_iff_glued]
  constructor
  · rintro ⟨hcoord, hsheet⟩
    have hδε : δ = ε := by
      apply Subtype.ext
      exact add_left_cancel hcoord
    refine ⟨hδε, ?_⟩
    rcases hsheet with hs | hm
    · left
      cases b <;> cases odd <;> cases other <;> simp_all
    · right
      have hback := H.sub_mem hm δ.property
      simpa using hback
  · rintro ⟨hδε, hflip | hθ⟩
    · subst ε
      exact ⟨rfl, Or.inl
        (congrArg (fun s : Bool => if s then !b else b) hflip)⟩
    · subst ε
      exact ⟨rfl, Or.inr (H.add_mem hθ δ.property)⟩

/-- The precise single-initial-state observational equivalence of words. -/
theorem wordAction_point_eq_iff (H : AddSubgroup G)
    (u v : List (H ⊕ Unit)) (θ : G) (b : Bool) :
    wordAction H u (point H θ b) =
      wordAction H v (point H θ b) ↔
    wordRotation H u = wordRotation H v ∧
      (wordFlipOdd H u = wordFlipOdd H v ∨ θ ∈ H) := by
  rw [wordAction_normal_form H u (point H θ b),
      wordAction_normal_form H v (point H θ b)]
  exact normal_forms_point_eq_iff H
    (wordRotation H u) (wordRotation H v)
    (wordFlipOdd H u) (wordFlipOdd H v) θ b

/-- At a glued starting point, parity cannot be recovered from the endpoint. -/
theorem wordAction_point_ignores_parity_on_gluing (H : AddSubgroup G)
    (u v : List (H ⊕ Unit)) (θ : G) (hθ : θ ∈ H) (b : Bool)
    (hrot : wordRotation H u = wordRotation H v) :
    wordAction H u (point H θ b) =
      wordAction H v (point H θ b) := by
  exact (wordAction_point_eq_iff H u v θ b).2
    ⟨hrot, Or.inr hθ⟩

/-- Off the glued locus, one known initial state distinguishes the full normal form. -/
theorem wordAction_point_faithful_off_gluing (H : AddSubgroup G)
    (u v : List (H ⊕ Unit)) (θ : G) (hθ : θ ∉ H) (b : Bool) :
    wordAction H u (point H θ b) =
      wordAction H v (point H θ b) ↔
    wordRotation H u = wordRotation H v ∧
      wordFlipOdd H u = wordFlipOdd H v := by
  rw [wordAction_point_eq_iff]
  constructor
  · rintro ⟨hrot, hflip | hm⟩
    · exact ⟨hrot, hflip⟩
    · exact False.elim (hθ hm)
  · rintro ⟨hrot, hflip⟩
    exact ⟨hrot, Or.inl hflip⟩

/-- The global quotient action distinguishes normal forms whenever H is proper. -/
theorem wordAction_global_eq_iff (H : AddSubgroup G)
    (hproper : ∃ θ : G, θ ∉ H) (u v : List (H ⊕ Unit)) :
    (∀ p : ClockSpace H, wordAction H u p = wordAction H v p) ↔
      wordRotation H u = wordRotation H v ∧
        wordFlipOdd H u = wordFlipOdd H v := by
  constructor
  · intro hall
    obtain ⟨θ, hθ⟩ := hproper
    exact (wordAction_point_faithful_off_gluing H u v θ hθ false).1
      (hall (point H θ false))
  · rintro ⟨hrot, hflip⟩ p
    exact same_normal_form_same_endpoint H u v hrot hflip p

end Abstract

/-- The non-rational sqrt(2) point witnesses normal-form observability on R/Z. -/
theorem sqrt_two_wordAction_point_eq_iff
    (u v : List (rationalAngles ⊕ Unit)) (b : Bool) :
    wordAction rationalAngles u
      (point rationalAngles ((Real.sqrt 2 : ℝ) : Angle) b) =
    wordAction rationalAngles v
      (point rationalAngles ((Real.sqrt 2 : ℝ) : Angle) b) ↔
    wordRotation rationalAngles u = wordRotation rationalAngles v ∧
      wordFlipOdd rationalAngles u = wordFlipOdd rationalAngles v :=
  wordAction_point_faithful_off_gluing rationalAngles
    u v ((Real.sqrt 2 : ℝ) : Angle) sqrt_two_angle_not_rational b

/-- On the actual rationally glued circle, all-state equality iff summaries agree. -/
theorem rational_wordAction_global_eq_iff
    (u v : List (rationalAngles ⊕ Unit)) :
    (∀ p : ClockSpace rationalAngles,
      wordAction rationalAngles u p = wordAction rationalAngles v p) ↔
    wordRotation rationalAngles u = wordRotation rationalAngles v ∧
      wordFlipOdd rationalAngles u = wordFlipOdd rationalAngles v :=
  wordAction_global_eq_iff rationalAngles
    ⟨((Real.sqrt 2 : ℝ) : Angle), sqrt_two_angle_not_rational⟩ u v

#print axioms point_eq_iff_glued
#print axioms wordAction_point_eq_iff
#print axioms wordAction_global_eq_iff
#print axioms rational_wordAction_global_eq_iff

end SphereClock.RationalGluing
