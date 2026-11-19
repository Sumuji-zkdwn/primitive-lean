/-!
# Pilot comparison: choice-dependent reconstruction and numerical obstruction

This is an abstract interface, NOT an IUT proof.  In particular, this file
does not construct a theta-link, an etale/Kummer reconstruction algorithm,
an Ind3-choice, or the required arithmetic lower bound on a container.

The original value can vary within a fiber of forgetting.  A reconstruction
with a choice parameter must cover *all* target values in that fiber; treating
a choice-dependent output as a single deterministic decoder loses information.

The log-volume result exposes the missing inequality without assuming it.
-/ 

noncomputable section

namespace LinearInputPilotComparison

/-- A target value can be reconstructed after forgetting by some choice. -/
def Reachable {A B S V : Type*}
    (forget : A -> B) (target : A -> V) (out : B -> S -> V) : Prop :=
  ∀ x, ∃ s, out (forget x) s = target x

/-- All original target values having a given forgotten observation. -/
def FiberTargets {A B V : Type*}
    (forget : A -> B) (target : A -> V) (b : B) : Set V :=
  {v | ∃ x, forget x = b /\ target x = v}

/-- Values available to the reconstruction procedure at a fixed observation. -/
def ChoiceValues {B S V : Type*} (out : B -> S -> V) (b : B) : Set V :=
  Set.range (out b)

/-- Exact range-cover criterion; choice parameters need not be unique. -/
theorem reachable_iff_fiber_covered {A B S V : Type*}
    (forget : A -> B) (target : A -> V) (out : B -> S -> V) :
    Reachable forget target out <->
      ∀ b, FiberTargets forget target b ⊆ ChoiceValues out b := by
  constructor
  · intro h b v hv
    obtain ⟨x, hfx, hq⟩ := hv
    obtain ⟨s, hs⟩ := h x
    refine ⟨s, ?_⟩
    calc
      out b s = out (forget x) s := by rw [hfx]
      _ = target x := hs
      _ = v := hq
  · intro h x
    exact h (forget x) ⟨x, rfl, rfl⟩

/-- The stronger notion: target is itself insensitive to forgotten fibers. -/
def FiberInvariant {A B V : Type*}
    (forget : A -> B) (target : A -> V) : Prop :=
  ∀ x y, forget x = forget y -> target x = target y

/-- Deterministic quotient factorization is equivalent to fiber invariance,
provided the target type is inhabited outside the observed range. -/
theorem factorization_iff_fiber_invariant {A B V : Type*} [Inhabited V]
    (forget : A -> B) (target : A -> V) :
    (∃ q : B -> V, ∀ x, q (forget x) = target x) <->
      FiberInvariant forget target := by
  constructor
  · rintro ⟨q, hq⟩ x y hxy
    calc
      target x = q (forget x) := (hq x).symm
      _ = q (forget y) := congrArg q hxy
      _ = target y := hq y
  · intro h
    classical
    let q : B -> V := fun b =>
      if hb : ∃ x : A, forget x = b then
        target (Classical.choose hb)
      else default
    refine ⟨q, ?_⟩
    intro x
    have hx : ∃ y : A, forget y = forget x := ⟨x, rfl⟩
    change (if hb : ∃ y : A, forget y = forget x then
      target (Classical.choose hb) else default) = target x
    rw [dite_eq_left hx]
    exact h (Classical.choose hx) x (Classical.choose_spec hx)

/-- A quotient target and an actual output witness produce reconstruction.
The witness is a separate input; it is not inferred from factorization. -/
theorem reachable_of_factor_and_witness {A B S V : Type*}
    (forget : A -> B) (target : A -> V) (out : B -> S -> V)
    (q : B -> V)
    (hfactor : ∀ x, q (forget x) = target x)
    (hwitness : ∀ b, ∃ s, out b s = q b) :
    Reachable forget target out := by
  intro x
  obtain ⟨s, hs⟩ := hwitness (forget x)
  exact ⟨s, hs.trans (hfactor x)⟩

/-- If choices make no difference, successful reconstruction forces the
target to descend through forgetting. The converse is false without a witness. -/
theorem reachable_choice_independent_implies_fiber_invariant {A B S V : Type*}
    (forget : A -> B) (target : A -> V) (out : B -> S -> V)
    (h : Reachable forget target out)
    (hirr : ∀ b s t, out b s = out b t) :
    FiberInvariant forget target := by
  intro x y hxy
  obtain ⟨sx, hx⟩ := h x
  obtain ⟨sy, hy⟩ := h y
  calc
    target x = out (forget x) sx := hx.symm
    _ = out (forget y) sy := by rw [hxy]; exact hirr (forget y) sx sy
    _ = target y := hy

/-- Numerical form of a comparison wall. Nothing is assumed about IUT. -/
def LogWall {A B S : Type*}
    (forget : A -> B) (target : A -> Real)
    (offset : B -> Real) (volume : B -> S -> Real) : Prop :=
  Reachable forget target (fun b s => offset b + volume b s)

/-- If every volume below a cap is realizable, the wall is equivalent to
the precise arithmetic bound on the target.  This is the bridge obligation. -/
theorem log_wall_iff_bound {A B S : Type*}
    (forget : A -> B) (target : A -> Real)
    (offset cap : B -> Real) (volume : B -> S -> Real)
    (hupper : ∀ b s, volume b s ≤ cap b)
    (hcomplete : ∀ b v, v ≤ cap b -> ∃ s, volume b s = v) :
    LogWall forget target offset volume <->
      ∀ x, target x - offset (forget x) ≤ cap (forget x) := by
  constructor
  · intro h x
    obtain ⟨s, hs⟩ := h x
    have hu := hupper (forget x) s
    change offset (forget x) + volume (forget x) s = target x at hs
    linarith
  · intro h x
    obtain ⟨s, hs⟩ :=
      hcomplete (forget x) (target x - offset (forget x)) (h x)
    refine ⟨s, ?_⟩
    change offset (forget x) + volume (forget x) s = target x
    rw [hs]
    ring

/-- The LANA/Scholze-Stix-shaped comparison in an abstract volume model:
offset = -scale*a and target = -a. This is NOT its arithmetic proof. -/
theorem scaled_pilot_witness_iff {S : Type*}
    (a scale cap : Real) (volume : S -> Real)
    (hupper : ∀ t, volume t ≤ cap)
    (hcomplete : ∀ v, v ≤ cap -> ∃ t, volume t = v) :
    (∃ t, -(scale * a) + volume t = -a) <->
      (scale - 1) * a ≤ cap := by
  constructor
  · rintro ⟨t, ht⟩
    have hu := hupper t
    nlinarith
  · intro hb
    obtain ⟨t, ht⟩ := hcomplete ((scale - 1) * a) hb
    refine ⟨t, ?_⟩
    rw [ht]
    ring

/-- A concrete full downward volume window, not an unconstrained oracle. -/
def truncatedVolume (cap t : Real) : Real := min t cap

theorem truncated_upper (cap t : Real) :
    truncatedVolume cap t ≤ cap := by
  exact min_le_right t cap

theorem truncated_complete (cap v : Real) (hv : v ≤ cap) :
    ∃ t : Real, truncatedVolume cap t = v := by
  refine ⟨v, ?_⟩
  exact min_eq_left hv

/-- ell=7, scale=14/3, a=1, cap=1: the comparison fails. -/
theorem ell7_small_container_obstruction :
    ¬ (∃ t : Real,
      -((14 / 3 : Real)) + truncatedVolume 1 t = -1) := by
  rintro ⟨t, ht⟩
  have hu := truncated_upper 1 t
  linarith

/-- The same target is attainable when the cap is 4 instead of 1. -/
theorem ell7_larger_container_witness :
    ∃ t : Real,
      -((14 / 3 : Real)) + truncatedVolume 4 t = -1 := by
  refine ⟨11 / 3, ?_⟩
  have hv : truncatedVolume 4 (11 / 3) = (11 / 3 : Real) := by
    change min (11 / 3 : Real) 4 = 11 / 3
    exact min_eq_left (by norm_num)
  rw [hv]
  norm_num

/-- A two-point forgetting that identifies every original state. -/
def constantForget (_ : Fin 2) : Fin 2 := 0

def distinctTarget (x : Fin 2) : Real := if x = 0 then 0 else 1

def choiceOutput (_ : Fin 2) (s : Fin 2) : Real := if s = 0 then 0 else 1

/-- Choice-dependent reconstruction can retain both original values, even
though no single-valued quotient target ∃. -/
theorem choice_range_can_cover_nonconstant_fiber :
    Reachable constantForget distinctTarget choiceOutput := by
  intro x
  exact ⟨x, rfl⟩

theorem choice_range_not_single_valued :
    ¬ (FiberInvariant constantForget distinctTarget) := by
  intro h
  have heq : distinctTarget (0 : Fin 2) = distinctTarget (1 : Fin 2) :=
    h 0 1 rfl
  norm_num [distinctTarget] at heq

theorem constant_forget_idempotent :
    LinearInputF0.Idempotent constantForget := by
  intro x
  rfl

/-- Existing F0 descent, even for the identity update, does not imply
the missing numerical comparison wall. -/
theorem f0_descent_does_not_force_wall :
    LinearInputF0Descent.Descends constantForget (fun x : Fin 2 => x) /\
    ¬ (Reachable constantForget (fun _ : Fin 2 => (-1 : Real))
      (fun (_ : Fin 2) (t : Real) =>
        -((14 / 3 : Real)) + truncatedVolume 1 t)) := by
  constructor
  · exact LinearInputF0Descent.identity_descends constant_forget_idempotent
  · intro h
    obtain ⟨t, ht⟩ := h (0 : Fin 2)
    exact ell7_small_container_obstruction ⟨t, ht⟩

end LinearInputPilotComparison
