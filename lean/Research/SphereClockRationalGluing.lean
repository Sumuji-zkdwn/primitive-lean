import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Tactic

/-!
# Sphere clock v0.2: rational-angle layer gluing

For any additive angle group G and subgroup H, take two copies of G.
The copies meet exactly at H; otherwise their layer bits remain distinct.
The quotient remembers this gluing. A common rotation by d descends
to the quotient if and only if d belongs to H.

We instantiate G with AddCircle 1 = R/Z, and H with the rational angles.
A full turn is the identity; an optional internal layer flip is an
extra operation, not a result of rotation or geometric holonomy.
-/

namespace SphereClock.RationalGluing

section Abstract

variable {G : Type*} [AddCommGroup G]

/-- Two layers meet at exactly the coordinates in H. -/
def Glued (H : AddSubgroup G) (x y : G × Bool) : Prop :=
  x.1 = y.1 ∧ (x.2 = y.2 ∨ x.1 ∈ H)

def gluedSetoid (H : AddSubgroup G) : Setoid (G × Bool) where
  r := Glued H
  iseqv := ⟨
    (by
      intro x
      exact ⟨rfl, Or.inl rfl⟩),
    (by
      intro x y h
      refine ⟨h.1.symm, ?_⟩
      rcases h.2 with hb | hm
      · exact Or.inl hb.symm
      · exact Or.inr (h.1 ▸ hm)),
    (by
      intro x y z hxy hyz
      refine ⟨hxy.1.trans hyz.1, ?_⟩
      rcases hxy.2 with hb | hm
      · rcases hyz.2 with hc | hn
        · exact Or.inl (hb.trans hc)
        · exact Or.inr (by simpa only [hxy.1] using hn)
      · exact Or.inr hm)⟩

abbrev ClockSpace (H : AddSubgroup G) := Quotient (gluedSetoid H)

def point (H : AddSubgroup G) (θ : G) (layer : Bool) : ClockSpace H :=
  Quotient.mk (gluedSetoid H) (θ, layer)

theorem layers_share_iff (H : AddSubgroup G) (θ : G) :
    Glued H (θ, false) (θ, true) ↔ θ ∈ H := by
  simp [Glued]

theorem points_share_iff (H : AddSubgroup G) (θ : G) :
    point H θ false = point H θ true ↔ θ ∈ H := by
  constructor
  · intro h
    exact (layers_share_iff H θ).mp (Quotient.exact h)
  · intro h
    exact Quotient.sound ((layers_share_iff H θ).mpr h)

/-- Rotate the actual branch-labeled angle, before taking the quotient. -/
def rotate (δ : G) (x : G × Bool) : G × Bool := (x.1 + δ, x.2)

theorem rotate_respects_of_mem (H : AddSubgroup G)
    (δ : G) (hδ : δ ∈ H) {x y : G × Bool}
    (h : Glued H x y) : Glued H (rotate δ x) (rotate δ y) := by
  change x.1 + δ = y.1 + δ ∧ (x.2 = y.2 ∨ x.1 + δ ∈ H)
  refine ⟨congrArg (fun a : G => a + δ) h.1, ?_⟩
  rcases h.2 with hb | hm
  · exact Or.inl hb
  · exact Or.inr (H.add_mem hm hδ)

/-- Main obstruction: common rotation respects rational gluing
    exactly when the rotation angle lies in the gluing subgroup. -/
theorem rotate_respects_iff (H : AddSubgroup G) (δ : G) :
    (∀ x y : G × Bool, Glued H x y →
      Glued H (rotate δ x) (rotate δ y)) ↔ δ ∈ H := by
  constructor
  · intro hall
    have h0 : Glued H ((0 : G), false) (0, true) :=
      ⟨rfl, Or.inr H.zero_mem⟩
    have hm := hall _ _ h0
    change (0 : G) + δ = (0 : G) + δ ∧
      (false = true ∨ (0 : G) + δ ∈ H) at hm
    rcases hm.2 with he | hδ
    · cases he
    · simpa using hδ
  · intro hδ x y h
    exact rotate_respects_of_mem H δ hδ h

/-- Every rational/subgroup shift induces a well-defined map of the quotient. -/
def rotateSpace (H : AddSubgroup G) (δ : G) (hδ : δ ∈ H) :
    ClockSpace H → ClockSpace H :=
  Quotient.lift
    (fun x => Quotient.mk (gluedSetoid H) (rotate δ x))
    (by
      intro x y h
      exact Quotient.sound (rotate_respects_of_mem H δ hδ h))

theorem rotateSpace_zero (H : AddSubgroup G) (p : ClockSpace H) :
    rotateSpace H 0 H.zero_mem p = p := by
  induction p using Quotient.inductionOn with
  | _ z =>
    change Quotient.mk (gluedSetoid H) (rotate 0 z) =
      Quotient.mk (gluedSetoid H) z
    cases z with
    | mk θ b =>
      simp [rotate]

theorem rotateSpace_add (H : AddSubgroup G)
    (δ ε : G) (hδ : δ ∈ H) (hε : ε ∈ H) (p : ClockSpace H) :
    rotateSpace H ε hε (rotateSpace H δ hδ p) =
      rotateSpace H (δ + ε) (H.add_mem hδ hε) p := by
  induction p using Quotient.inductionOn with
  | _ z =>
    change Quotient.mk (gluedSetoid H) (rotate ε (rotate δ z)) =
      Quotient.mk (gluedSetoid H) (rotate (δ + ε) z)
    cases z with
    | mk θ b =>
      simp [rotate, add_assoc]

/-- Explicit extra operation, not inferred from a revolution. -/
def flip (x : G × Bool) : G × Bool := (x.1, !x.2)

def flipSpace (H : AddSubgroup G) : ClockSpace H → ClockSpace H :=
  Quotient.lift
    (fun x => Quotient.mk (gluedSetoid H) (flip x))
    (by
      intro x y h
      apply Quotient.sound
      refine ⟨h.1, ?_⟩
      rcases h.2 with hb | hm
      · exact Or.inl (congrArg not hb)
      · exact Or.inr hm)

theorem flip_fixed_iff (H : AddSubgroup G) (θ : G) (b : Bool) :
    flipSpace H (point H θ b) = point H θ b ↔ θ ∈ H := by
  constructor
  · intro h
    have hh : Glued H (θ, !b) (θ, b) := Quotient.exact h
    rcases hh.2 with hbool | hm
    · cases b <;> cases hbool
    · exact hm
  · intro hm
    exact Quotient.sound (show Glued H (θ, !b) (θ, b)
      from ⟨rfl, Or.inr hm⟩)

theorem flipSpace_involution (H : AddSubgroup G) (p : ClockSpace H) :
    flipSpace H (flipSpace H p) = p := by
  induction p using Quotient.inductionOn with
  | _ z =>
    change Quotient.mk (gluedSetoid H) (flip (flip z)) =
      Quotient.mk (gluedSetoid H) z
    cases z with
    | mk θ b =>
      simp [flip]

end Abstract

/-! The actual clock angles, with one full turn identified with zero. -/

abbrev Angle := AddCircle (1 : ℝ)

/-- Exactly the image of rational angular coordinates in R/Z. -/
def rationalAngles : AddSubgroup Angle where
  carrier := {θ | ∃ q : ℚ, ((q : ℝ) : Angle) = θ}
  zero_mem' := by
    change ∃ q : ℚ, ((q : ℝ) : Angle) = 0
    exact ⟨0, by simpa using (AddCircle.coe_zero (1 : ℝ))⟩
  add_mem' := by
    intro a b ha hb
    obtain ⟨qa, hqa⟩ := ha
    obtain ⟨qb, hqb⟩ := hb
    refine ⟨qa + qb, ?_⟩
    calc
      (((qa + qb : ℚ) : ℝ) : Angle) =
          (((qa : ℝ) + (qb : ℝ)) : Angle) := by simp only [Rat.cast_add]
      _ = ((qa : ℝ) : Angle) + ((qb : ℝ) : Angle) :=
        AddCircle.coe_add (1 : ℝ) (qa : ℝ) (qb : ℝ)
      _ = a + b := by rw [hqa, hqb]
  neg_mem' := by
    intro a ha
    obtain ⟨q, hq⟩ := ha
    refine ⟨-q, ?_⟩
    calc
      (((-q : ℚ) : ℝ) : Angle) = ((-(q : ℝ)) : Angle) := by
        simp only [Rat.cast_neg]
      _ = -((q : ℝ) : Angle) := AddCircle.coe_neg (1 : ℝ)
      _ = -a := by rw [hq]

/-- A rational angular position joins both layers. -/
theorem rational_point_joins (q : ℚ) :
    point rationalAngles (((q : ℝ) : Angle)) false =
      point rationalAngles (((q : ℝ) : Angle)) true := by
  exact (points_share_iff rationalAngles _).2 ⟨q, rfl⟩

theorem one_turn_is_zero : ((1 : ℝ) : Angle) = 0 :=
  AddCircle.coe_period (1 : ℝ)

theorem one_turn_is_rational : ((1 : ℝ) : Angle) ∈ rationalAngles := by
  rw [one_turn_is_zero]
  exact rationalAngles.zero_mem

/-- Position really returns after 1 full turn on the circle quotient. -/
theorem full_turn_is_identity (p : ClockSpace rationalAngles) :
    rotateSpace rationalAngles ((1 : ℝ) : Angle) one_turn_is_rational p = p := by
  simpa only [one_turn_is_zero] using (rotateSpace_zero rationalAngles p)

/-- Two glued layers can become distinct under a non-rational rotation
    of their *representatives*. Such a rotation does not descend to
    a well-defined map of the quotient; this is not quotient dynamics. -/
theorem hidden_layer_reappears (δ : Angle) (hδ : δ ∉ rationalAngles) :
    point rationalAngles 0 false = point rationalAngles 0 true ∧
    point rationalAngles δ false ≠ point rationalAngles δ true := by
  constructor
  · exact (points_share_iff rationalAngles 0).2 rationalAngles.zero_mem
  · intro h
    exact hδ ((points_share_iff rationalAngles δ).1 h)

/-- A full turn + an *explicitly added* internal switch returns
    the angle but may change a layer-distinguishable state. -/
def loopWithSwitch (p : ClockSpace rationalAngles) : ClockSpace rationalAngles :=
  flipSpace rationalAngles
    (rotateSpace rationalAngles ((1 : ℝ) : Angle) one_turn_is_rational p)

theorem switched_loop_fixes_rational (θ : Angle)
    (hθ : θ ∈ rationalAngles) (b : Bool) :
    loopWithSwitch (point rationalAngles θ b) =
      point rationalAngles θ b := by
  unfold loopWithSwitch
  rw [full_turn_is_identity]
  exact (flip_fixed_iff rationalAngles θ b).2 hθ

theorem switched_loop_changes_nonrational (θ : Angle)
    (hθ : θ ∉ rationalAngles) (b : Bool) :
    loopWithSwitch (point rationalAngles θ b) ≠
      point rationalAngles θ b := by
  unfold loopWithSwitch
  rw [full_turn_is_identity]
  intro h
  exact hθ ((flip_fixed_iff rationalAngles θ b).1 h)

#print axioms rotate_respects_iff
#print axioms full_turn_is_identity
#print axioms hidden_layer_reappears
#print axioms switched_loop_changes_nonrational

end SphereClock.RationalGluing
