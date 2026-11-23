import Mathlib

/-!
# Delayed-aether finite cochains: exact exterior-derivative identities

This module isolates a *small proved component* of the ten-stage delayed-hardening
aether experiment. It formalizes the commuting finite differences of a flat
translation lattice and the preservation of a closed 2-cochain under an exact
1-cochain update. The coefficients can be specialized to \`ZMod 2\` for the
binary plaquette model of stage 10.

This does **not** construct a curved Lorentzian metric, Einstein constraints,
gravity, solitons, or a physical causal memory law.
-/

namespace DelayedAether

variable {X : Type*} [AddCommGroup X]
variable {R : Type*} [CommRing R]

/-- A translation-lattice field with coefficients in a commutative ring. -/
abbrev C0 (X : Type*) (R : Type*) := X → R

/-- Three oriented components of a discrete 1-cochain. -/
structure OneForm (X : Type*) (R : Type*) where
  x : C0 X R
  y : C0 X R
  z : C0 X R

/-- Components of a discrete 2-cochain in three spatial directions. -/
structure TwoForm (X : Type*) (R : Type*) where
  xy : C0 X R
  xz : C0 X R
  yz : C0 X R

/-- Forward difference along a translation vector. -/
def forward (v : X) (f : C0 X R) : C0 X R :=
  fun p => f (p + v) - f p

/-- Translation differences commute on an abelian spatial lattice. -/
theorem forward_comm (v w : X) (f : C0 X R) :
    forward v (forward w f) = forward w (forward v f) := by
  funext p
  change (f (p + v + w) - f (p + v)) - (f (p + w) - f p) =
    (f (p + w + v) - f (p + w)) - (f (p + v) - f p)
  have h : p + v + w = p + w + v := by abel
  rw [h]
  ring

/-- Forward difference distributes over pointwise addition. -/
theorem forward_add (v : X) (f g : C0 X R) (p : X) :
    forward v (fun q => f q + g q) p =
      forward v f p + forward v g p := by
  simp only [forward]
  ring

/-- Forward difference distributes over pointwise subtraction. -/
theorem forward_sub (v : X) (f g : C0 X R) (p : X) :
    forward v (fun q => f q - g q) p =
      forward v f p - forward v g p := by
  simp only [forward]
  ring

/-- A discrete gradient represented as an oriented 1-cochain. -/
def d0 (vx vy vz : X) (f : C0 X R) : OneForm X R :=
  { x := forward vx f, y := forward vy f, z := forward vz f }

/-- Discrete exterior derivative from 1- to 2-cochains. -/
def d1 (vx vy vz : X) (a : OneForm X R) : TwoForm X R :=
  { xy := fun p => forward vx a.y p - forward vy a.x p
    xz := fun p => forward vx a.z p - forward vz a.x p
    yz := fun p => forward vy a.z p - forward vz a.y p }

/-- Discrete exterior derivative from 2- to 3-cochains. -/
def d2 (vx vy vz : X) (b : TwoForm X R) : C0 X R :=
  fun p => forward vx b.yz p - forward vy b.xz p + forward vz b.xy p

/-- Exterior differentiation of a discrete gradient has zero xy component. -/
theorem d1_d0_xy (vx vy vz : X) (f : C0 X R) :
    (d1 vx vy vz (d0 vx vy vz f)).xy = fun _ => 0 := by
  funext p
  change forward vx (forward vy f) p - forward vy (forward vx f) p = 0
  rw [congrFun (forward_comm vx vy f) p]
  ring

/-- Exterior differentiation of a discrete gradient has zero xz component. -/
theorem d1_d0_xz (vx vy vz : X) (f : C0 X R) :
    (d1 vx vy vz (d0 vx vy vz f)).xz = fun _ => 0 := by
  funext p
  change forward vx (forward vz f) p - forward vz (forward vx f) p = 0
  rw [congrFun (forward_comm vx vz f) p]
  ring

/-- Exterior differentiation of a discrete gradient has zero yz component. -/
theorem d1_d0_yz (vx vy vz : X) (f : C0 X R) :
    (d1 vx vy vz (d0 vx vy vz f)).yz = fun _ => 0 := by
  funext p
  change forward vy (forward vz f) p - forward vz (forward vy f) p = 0
  rw [congrFun (forward_comm vy vz f) p]
  ring

/-- \`d₂ ∘ d₁ = 0\`: exact discrete Bianchi closure for commuting translations. -/
theorem d2_d1_zero (vx vy vz : X) (a : OneForm X R) :
    d2 vx vy vz (d1 vx vy vz a) = fun _ => 0 := by
  funext p
  change
    forward vx (fun q => forward vy a.z q - forward vz a.y q) p -
      forward vy (fun q => forward vx a.z q - forward vz a.x q) p +
      forward vz (fun q => forward vx a.y q - forward vy a.x q) p = 0
  rw [forward_sub, forward_sub, forward_sub]
  have hxy :
      forward vx (forward vy a.z) p = forward vy (forward vx a.z) p :=
    congrFun (forward_comm vx vy a.z) p
  have hxz :
      forward vx (forward vz a.y) p = forward vz (forward vx a.y) p :=
    congrFun (forward_comm vx vz a.y) p
  have hyz :
      forward vy (forward vz a.x) p = forward vz (forward vy a.x) p :=
    congrFun (forward_comm vy vz a.x) p
  rw [hxy, hxz, hyz]
  ring

/-- Pointwise sum of discrete 2-cochains. -/
def addTwo (b c : TwoForm X R) : TwoForm X R :=
  { xy := fun p => b.xy p + c.xy p
    xz := fun p => b.xz p + c.xz p
    yz := fun p => b.yz p + c.yz p }

/-- The 2-to-3 differential is linear. -/
theorem d2_add (vx vy vz : X) (b c : TwoForm X R) :
    d2 vx vy vz (addTwo b c) =
      fun p => d2 vx vy vz b p + d2 vx vy vz c p := by
  funext p
  change
    forward vx (fun q => b.yz q + c.yz q) p -
      forward vy (fun q => b.xz q + c.xz q) p +
      forward vz (fun q => b.xy q + c.xy q) p =
    (forward vx b.yz p - forward vy b.xz p + forward vz b.xy p) +
      (forward vx c.yz p - forward vy c.xz p + forward vz c.xy p)
  rw [forward_add, forward_add, forward_add]
  ring

/-- A local cochain update: new curvature = old curvature + exact change. -/
def update (vx vy vz : X) (b : TwoForm X R)
    (a : OneForm X R) : TwoForm X R :=
  addTwo b (d1 vx vy vz a)

/-- The 3-form closure value is invariant under any exact local update. -/
theorem d2_update (vx vy vz : X) (b : TwoForm X R)
    (a : OneForm X R) :
    d2 vx vy vz (update vx vy vz b a) = d2 vx vy vz b := by
  change d2 vx vy vz (addTwo b (d1 vx vy vz a)) = d2 vx vy vz b
  rw [d2_add, d2_d1_zero]
  funext p
  simp

/-- A closed 2-cochain stays closed after a local update. -/
theorem closed_update (vx vy vz : X) (b : TwoForm X R)
    (a : OneForm X R) (hb : d2 vx vy vz b = fun _ => 0) :
    d2 vx vy vz (update vx vy vz b a) = fun _ => 0 := by
  rw [d2_update]
  exact hb

/-- Closure is preserved after two successive updates. -/
theorem closed_two_updates (vx vy vz : X) (b : TwoForm X R)
    (a₁ a₂ : OneForm X R) (hb : d2 vx vy vz b = fun _ => 0) :
    d2 vx vy vz (update vx vy vz (update vx vy vz b a₁) a₂) =
      fun _ => 0 := by
  apply closed_update
  exact closed_update vx vy vz b a₁ hb

/-- An internal memory state linearly tracks its target field. -/
def memoryStep {Y : Type*} (weight : R) (m f : C0 Y R) : C0 Y R :=
  fun p => (1 - weight) * m p + weight * f p

/-- If memory already matches the field, an affine step leaves it unchanged. -/
theorem memoryStep_fixed {Y : Type*} (weight : R) (f : C0 Y R) :
    memoryStep weight f f = f := by
  funext p
  simp only [memoryStep]
  ring

/-- The memory update is a relaxation toward its new target. -/
theorem memoryStep_difference {Y : Type*} (weight : R) (m f : C0 Y R) :
    memoryStep weight m f = fun p => m p + weight * (f p - m p) := by
  funext p
  simp only [memoryStep]
  ring

/-- Stage 10's \`ZMod 2\` coefficient system is a special case. -/
theorem binary_closed_update (vx vy vz : X)
    (b : TwoForm X (ZMod 2)) (a : OneForm X (ZMod 2))
    (hb : d2 vx vy vz b = fun _ => 0) :
    d2 vx vy vz (update vx vy vz b a) = fun _ => 0 :=
  closed_update vx vy vz b a hb

end DelayedAether
