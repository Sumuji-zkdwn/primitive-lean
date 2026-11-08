import Research.SphereClockRationalGluing

/-!
# Sphere clock: normal form of finite permitted operation words

Only the existing quotient maps `rotateSpace` (for an element of H)
and the explicitly stipulated `flipSpace` are used. A word is a list
of either a subgroup rotation (`Sum.inl`) or a layer flip (`Sum.inr ()`).
The head of a word acts last (functional-composition convention).

These claims concern the glued quotient, not physical rotation,
holonomy or quantum phenomena.
-/

namespace SphereClock.RationalGluing

section Abstract

variable {G : Type*} [AddCommGroup G]

/-- An admissible quotient rotation commutes with the extra layer flip. -/
theorem rotateSpace_flipSpace_commute (H : AddSubgroup G)
    (δ : G) (hδ : δ ∈ H) (p : ClockSpace H) :
    rotateSpace H δ hδ (flipSpace H p) =
      flipSpace H (rotateSpace H δ hδ p) := by
  induction p using Quotient.inductionOn with
  | _ z =>
    change Quotient.mk (gluedSetoid H) (rotate δ (flip z)) =
      Quotient.mk (gluedSetoid H) (flip (rotate δ z))
    cases z with
    | mk θ b => rfl

/-- Composition of two rotations, reusing `rotateSpace_add`. -/
theorem rotateSpace_add_subtype (H : AddSubgroup G)
    (δ ε : H) (p : ClockSpace H) :
    rotateSpace H (δ : G) δ.property
        (rotateSpace H (ε : G) ε.property p) =
      rotateSpace H ((δ + ε : H) : G) (δ + ε).property p := by
  simpa only [AddSubgroup.coe_add, add_comm] using
    (rotateSpace_add H (ε : G) (δ : G) ε.property δ.property p)

/-- A word over the existing two operations; no new operation algebra. -/
def wordAction (H : AddSubgroup G) (word : List (H ⊕ Unit))
    (p : ClockSpace H) : ClockSpace H :=
  match word with
  | [] => p
  | Sum.inl δ :: rest =>
      rotateSpace H (δ : G) δ.property (wordAction H rest p)
  | Sum.inr _ :: rest => flipSpace H (wordAction H rest p)

/-- Sum of all permitted rotation increments in a word. -/
def wordRotation (H : AddSubgroup G) : List (H ⊕ Unit) → H
  | [] => 0
  | Sum.inl δ :: rest => δ + wordRotation H rest
  | Sum.inr _ :: rest => wordRotation H rest

/-- Whether the number of explicit layer flips is odd. -/
def wordFlipOdd (H : AddSubgroup G) : List (H ⊕ Unit) → Bool
  | [] => false
  | Sum.inl _ :: rest => wordFlipOdd H rest
  | Sum.inr _ :: rest => !(wordFlipOdd H rest)

/-- Every finite operation word reduces to total rotation and flip parity. -/
theorem wordAction_normal_form (H : AddSubgroup G)
    (word : List (H ⊕ Unit)) (p : ClockSpace H) :
    wordAction H word p =
      if wordFlipOdd H word then
        flipSpace H (rotateSpace H (wordRotation H word : G)
          (wordRotation H word).property p)
      else
        rotateSpace H (wordRotation H word : G)
          (wordRotation H word).property p := by
  induction word with
  | nil =>
      simpa [wordAction, wordRotation, wordFlipOdd] using
        (rotateSpace_zero H p).symm
  | cons op rest ih =>
      cases op with
      | inl δ =>
          change rotateSpace H (δ : G) δ.property (wordAction H rest p) =
            if wordFlipOdd H rest then
              flipSpace H (rotateSpace H ((δ + wordRotation H rest : H) : G)
                (δ + wordRotation H rest).property p)
            else
              rotateSpace H ((δ + wordRotation H rest : H) : G)
                (δ + wordRotation H rest).property p
          rw [ih]
          by_cases hb : wordFlipOdd H rest
          · simp only [if_pos hb]
            rw [rotateSpace_flipSpace_commute]
            exact congrArg (flipSpace H)
              (rotateSpace_add_subtype H δ (wordRotation H rest) p)
          · simp only [if_neg hb]
            exact rotateSpace_add_subtype H δ (wordRotation H rest) p
      | inr u =>
          change flipSpace H (wordAction H rest p) =
            if !(wordFlipOdd H rest) then
              flipSpace H (rotateSpace H (wordRotation H rest : G)
                (wordRotation H rest).property p)
            else
              rotateSpace H (wordRotation H rest : G)
                (wordRotation H rest).property p
          rw [ih]
          by_cases hb : wordFlipOdd H rest
          · simp [hb, flipSpace_involution]
          · simp [hb]

/-- Equal summaries give equal endpoints for every starting state. -/
theorem same_normal_form_same_endpoint (H : AddSubgroup G)
    (a b : List (H ⊕ Unit))
    (hrot : wordRotation H a = wordRotation H b)
    (hflip : wordFlipOdd H a = wordFlipOdd H b)
    (p : ClockSpace H) :
    wordAction H a p = wordAction H b p := by
  rw [wordAction_normal_form H a p, wordAction_normal_form H b p, hrot, hflip]

/-- Rotation--flip and flip--rotation have the same endpoint. -/
theorem switched_orders_same_endpoint (H : AddSubgroup G)
    (δ : H) (p : ClockSpace H) :
    wordAction H [Sum.inl δ, Sum.inr ()] p =
      wordAction H [Sum.inr (), Sum.inl δ] p := by
  change rotateSpace H (δ : G) δ.property (flipSpace H p) =
    flipSpace H (rotateSpace H (δ : G) δ.property p)
  exact rotateSpace_flipSpace_commute H (δ : G) δ.property p

/-- A nonzero rotation and a layer flip give different first states. -/
theorem nonzero_rotation_distinguished_from_flip (H : AddSubgroup G)
    (δ : H) (hδ : (δ : G) ≠ 0) (p : ClockSpace H) :
    rotateSpace H (δ : G) δ.property p ≠ flipSpace H p := by
  induction p using Quotient.inductionOn with
  | _ z =>
    cases z with
    | mk θ b =>
      intro heq
      change point H (θ + (δ : G)) b = point H θ (!b) at heq
      have hcoord : θ + (δ : G) = θ := (Quotient.exact heq).1
      have hz : (δ : G) = 0 :=
        add_left_cancel (show θ + (δ : G) = θ + (0 : G) by
          simpa only [add_zero] using hcoord)
      exact hδ hz

/-- Endpoint order-loss versus a sampled intermediate-state observation. -/
theorem reordered_word_history_witness (H : AddSubgroup G)
    (δ : H) (hδ : (δ : G) ≠ 0) (p : ClockSpace H) :
    (flipSpace H (rotateSpace H (δ : G) δ.property p) =
      rotateSpace H (δ : G) δ.property (flipSpace H p)) ∧
    (rotateSpace H (δ : G) δ.property p ≠ flipSpace H p) := by
  exact ⟨(rotateSpace_flipSpace_commute H (δ : G) δ.property p).symm,
    nonzero_rotation_distinguished_from_flip H δ hδ p⟩

/-- At a glued coordinate, even flip parity itself is invisible. -/
theorem flip_parity_invisible_at_gluing (H : AddSubgroup G)
    (θ : G) (hθ : θ ∈ H) (b : Bool) :
    flipSpace H (point H θ b) = point H θ b :=
  (flip_fixed_iff H θ b).2 hθ

end Abstract

#print axioms rotateSpace_flipSpace_commute
#print axioms wordAction_normal_form
#print axioms same_normal_form_same_endpoint
#print axioms reordered_word_history_witness

end SphereClock.RationalGluing
