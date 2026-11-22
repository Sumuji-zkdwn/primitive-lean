import Mathlib.Tactic

/-!
# Gauge equivalence of non-Abelian geometric lifts (finite scaffold)

A finite base of three labeled sites carries an oriented link assignment in an
arbitrary group G. Each base site has a G-fibre. Horizontal edges carry the link
value; vertical edges act by right multiplication by a selected generator.
Local changes of fibre frame act by left multiplication, and preserve both
kinds of lifted edges. The triangle's closed-loop transport is transformed by
conjugation. This is the discrete analogue of gauge covariance in Kaluza--Klein
bundle geometry, NOT a claim of reconstructed Yang--Mills field equations.
-/

namespace NonAbelianMetricHolonomy

variable {G : Type*} [Group G]

abbrev Link (G : Type*) := Fin 3 → Fin 3 → G
abbrev Point (G : Type*) := Fin 3 × G

/-- Change of local G-frame at each base site. -/
def reframe (h : Fin 3 → G) (U : Link G) : Link G :=
  fun i j => h j * U i j * (h i)⁻¹

/-- The corresponding relabelling of the points in the lifted space. -/
def move (h : Fin 3 → G) (p : Point G) : Point G :=
  (p.1, h p.1 * p.2)

/-- Transport a fibre coordinate across an oriented base edge. -/
def transport (U : Link G) (i j : Fin 3) (g : G) : G :=
  U i j * g

theorem transport_covariant (h : Fin 3 → G) (U : Link G)
    (i j : Fin 3) (g : G) :
    transport (reframe h U) i j (h i * g) =
      h j * transport U i j g := by
  simp [transport, reframe, mul_assoc]

/-- A gauge change cannot modify the holonomy except by conjugation. -/
def holonomy (U : Link G) : G :=
  U 2 0 * U 1 2 * U 0 1

theorem holonomy_conjugacy (h : Fin 3 → G) (U : Link G) :
    holonomy (reframe h U) =
      h 0 * holonomy U * (h 0)⁻¹ := by
  simp [holonomy, reframe]
  group

/-- Directed horizontal adjacency on the lifted 3-site space. -/
def horizontal (U : Link G) (p q : Point G) : Prop :=
  p.1 ≠ q.1 ∧ q.2 = transport U p.1 q.1 p.2

/-- Generator-defined directed adjacency within each fibre. -/
def vertical (generators : Set G) (p q : Point G) : Prop :=
  p.1 = q.1 ∧ ∃ s ∈ generators, q.2 = p.2 * s

def edge (U : Link G) (generators : Set G) (p q : Point G) : Prop :=
  horizontal U p q ∨ vertical generators p q

theorem horizontal_covariant (h : Fin 3 → G) (U : Link G)
    (p q : Point G) (hpq : horizontal U p q) :
    horizontal (reframe h U) (move h p) (move h q) := by
  rcases hpq with ⟨hne, hq⟩
  constructor
  · simpa [move] using hne
  · change h q.1 * q.2 = transport (reframe h U) p.1 q.1 (h p.1 * p.2)
    rw [hq, transport_covariant]

theorem vertical_covariant (h : Fin 3 → G) (generators : Set G)
    (p q : Point G) (hpq : vertical generators p q) :
    vertical generators (move h p) (move h q) := by
  rcases hpq with ⟨heq, ⟨s, hs, hq⟩⟩
  constructor
  · simpa [move] using heq
  · refine ⟨s, hs, ?_⟩
    change h q.1 * q.2 = (h p.1 * p.2) * s
    rw [← heq, hq, mul_assoc]

theorem edge_covariant (h : Fin 3 → G) (U : Link G)
    (generators : Set G) (p q : Point G)
    (hpq : edge U generators p q) :
    edge (reframe h U) generators (move h p) (move h q) := by
  rcases hpq with hh | hv
  · exact Or.inl (horizontal_covariant h U p q hh)
  · exact Or.inr (vertical_covariant h generators p q hv)

/-- Reframing is a bijection of the geometric fibre over every site. -/
theorem move_inverse (h : Fin 3 → G) (p : Point G) :
    move (fun i => (h i)⁻¹) (move h p) = p := by
  cases p with
  | mk i g => simp [move]

/-- A small faithful noncommutative finite subgroup is already available. -/
def swap01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
def swap12 : Equiv.Perm (Fin 3) := Equiv.swap 1 2

theorem swaps_do_not_commute : swap01 * swap12 ≠ swap12 * swap01 := by
  decide

/-- Distinct oriented paths can act differently on a fixed fibre point. -/
theorem noncommuting_transport :
    (swap01 * swap12) * (1 : Equiv.Perm (Fin 3)) ≠
    (swap12 * swap01) * (1 : Equiv.Perm (Fin 3)) := by
  simpa using swaps_do_not_commute

end NonAbelianMetricHolonomy
