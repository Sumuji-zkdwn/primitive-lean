/-!
# F16 signed-basis comparison holonomy and F0 observation descent

F16 sign convention is copied from the user's 2026-10-22
E_atlas_F16_smooth_v4_2026-10-22.zip, nested source
sources/f16_v2/F16_bridge_2026-10-22/sedenion16.py
(SHA-256 a42a94fcc979530946565f720498036b8d2cbc79ebc5aae96b0b68d47fea68ce).

Finite F16 signed basis multiplication: e_a * e_b = eps(a,b) e_(a XOR b).
Observation forgets bit 8 but preserves sign.  Omega is the discrepancy
on two representatives of the same observed state.

This does not identify the non-associative sedenion algebra with any field
extension, any Galois group, or smooth Levi-Civita holonomy.
-/

noncomputable section

namespace LinearInputF16Holonomy

/-- The explicit Cayley-Dickson sign matrix for the 16 signed basis units. -/
def epsTable : Array (Array ℤ) := #[
  #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  #[1, -1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1],
  #[1, -1, -1, 1, 1, 1, -1, -1, 1, 1, -1, -1, -1, -1, 1, 1],
  #[1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1, 1],
  #[1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1],
  #[1, 1, -1, 1, -1, -1, -1, 1, 1, -1, 1, -1, 1, -1, 1, -1],
  #[1, 1, 1, -1, -1, 1, -1, -1, 1, -1, -1, 1, 1, -1, -1, 1],
  #[1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, -1],
  #[1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1],
  #[1, 1, -1, 1, -1, 1, 1, -1, -1, -1, -1, 1, -1, 1, 1, -1],
  #[1, 1, 1, -1, -1, -1, 1, 1, -1, 1, -1, -1, -1, -1, 1, 1],
  #[1, -1, 1, 1, -1, 1, -1, 1, -1, -1, 1, -1, -1, 1, -1, 1],
  #[1, 1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 1, -1, -1, -1, -1],
  #[1, -1, 1, -1, 1, 1, 1, -1, -1, -1, 1, -1, 1, -1, 1, -1],
  #[1, -1, -1, 1, 1, -1, 1, 1, -1, -1, -1, 1, 1, -1, -1, 1],
  #[1, 1, -1, -1, 1, 1, -1, 1, -1, 1, -1, -1, 1, 1, -1, -1]
]

def eps (a b : Fin 16) : ℤ := (epsTable[a.val]!)[b.val]!

def low (a : Fin 8) : Fin 16 :=
  ⟨a.val, by have := a.isLt; omega⟩

def high (a : Fin 8) : Fin 16 :=
  ⟨a.val + 8, by have := a.isLt; omega⟩

/-- Sign mismatch from forgetting one bit of the signed F16 basis. -/
def omega (a : Fin 8) (b : Fin 16) : ℤ := eps (low a) b * eps (high a) b

/-- Exact classification of all 128 comparison squares. -/
theorem omega_by_probe (a : Fin 8) (b : Fin 16) :
    omega a b = (if b.val = 0 ∨ 9 ≤ b.val then 1 else -1) := by
  fin_cases a <;> fin_cases b <;> decide

/-- The finite obstruction is independent of the forgotten representative. -/
theorem omega_independent_of_low (a c : Fin 8) (b : Fin 16) :
    omega a b = omega c b := by
  rw [omega_by_probe, omega_by_probe]

theorem omega_negative_iff (a : Fin 8) (b : Fin 16) :
    omega a b = -1 ↔ 1 ≤ b.val ∧ b.val ≤ 8 := by
  fin_cases a <;> fin_cases b <;> decide

/-- There are 64 negative squares in the 8 by 16 finite table. -/
theorem negative_square_count :
    (Finset.univ.filter (fun p : Fin 8 × Fin 16 => omega p.1 p.2 = -1)).card = 64 := by
  decide

/-- The product of all eight local discrepancies is always +1,
even when every single square is nontrivial. -/
theorem whole_probe_product_forgets (b : Fin 16) :
    (∏ a : Fin 8, omega a b) = 1 := by
  fin_cases b <;> decide

/-- Forgetting a high index bit is an actual idempotent F0 retraction. -/
def forgetIndex (a : Fin 16) : Fin 16 :=
  ⟨a.val % 8, by
    have h : a.val % 8 < 8 := Nat.mod_lt _ (by decide)
    omega⟩

def forgetSigned (s : Bool × Fin 16) : Bool × Fin 16 :=
  (s.1, forgetIndex s.2)

theorem forgetSigned_idempotent : LinearInputF0.Idempotent forgetSigned := by
  rintro ⟨s, a⟩
  cases s <;> fin_cases a <;> decide

/-- Signed basis right multiplication, using bitwise XOR for the basis index. -/
def rightIndex (a b : Fin 16) : Fin 16 :=
  ⟨(Nat.xor a.val b.val) % 16, Nat.mod_lt _ (by decide)⟩

def rightSigned (b : Fin 16) (s : Bool × Fin 16) : Bool × Fin 16 :=
  ((if eps s.2 b = -1 then !s.1 else s.1), rightIndex s.2 b)

/-- Observable result, as a canonical signed representative with bit 8 erased. -/
def observedRight (b : Fin 16) (s : Bool × Fin 16) : Bool × Fin 16 :=
  forgetSigned (rightSigned b s)

/-- Exact descent criterion: all future right-multiplication observables depend
only on the current coarse state exactly for probes 0 and 9..15.  This is the
existing F0 Compatible predicate applied to an explicit finite action. -/
theorem observedRight_compatible_iff (b : Fin 16) :
    LinearInputF0.Compatible forgetSigned
      (fun s (_ : Fin 1) => observedRight b s) ↔
        (b.val = 0 ∨ 9 ≤ b.val) := by
  fin_cases b <;> decide

end LinearInputF16Holonomy
