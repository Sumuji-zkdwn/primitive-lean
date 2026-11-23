import Mathlib.Tactic
import Research.KKHopfHomeo
import Research.KKHopfTwoSections
import Research.KKHopfPhaseUnique

/-!
# Explicit algebraic local trivialization of the Hopf circle action

The north domain is the inverse image under Hopf of {w > -1}.
We construct the actual bijection with (base patch) × S1 using
(1) the north section, and (2) fibre phase recovered by real dot/skew.
It is not yet declared a homeomorphism or a Mathlib principal bundle.
-/

namespace KKHopfNorthTriv
open KKHopfGlobalAlgebra KKHopfQuotient

abbrev UnitPhase := {u : Fin 2 → ℝ // u 0 ^ 2 + u 1 ^ 2 = 1}
abbrev NorthBase := {b : Sphere2 // 0 < 1 + b.1 2}
abbrev NorthTotal := {x : Sphere3 // 0 < 1 + (proj x).1 2}

def base (X : NorthTotal) : NorthBase := ⟨proj X.1, X.2⟩

noncomputable def section (b : NorthBase) : Sphere3 := by
  let u : ℝ := b.1.1 0
  let v : ℝ := b.1.1 1
  let w : ℝ := b.1.1 2
  have hs : u^2+v^2+w^2=1 := b.1.2
  have hp : 0 < 1+w := b.2
  exact ⟨KKHopfSurjective.northVec u v w,
    (KKHopfSurjective.north_chart u v w hs hp).1⟩

theorem section_projects (b : NorthBase) : proj (section b) = b.1 := by
  apply Subtype.ext
  funext i
  obtain ⟨_,hu,hv,hw⟩ := KKHopfSurjective.north_chart
      (b.1.1 0) (b.1.1 1) (b.1.1 2) b.1.2 b.2
  fin_cases i <;> simp [proj,section,hu,hv,hw]

private theorem exists_rotation (X : NorthTotal) :
    ∃ C S : ℝ, C^2+S^2=1 ∧
      rotate C S (section (base X)).1 = X.1.1 := by
  have hp : proj (section (base X)) = proj X.1 := by
    rw [section_projects]
    rfl
  have hx : hopfX (section (base X)).1 = hopfX X.1.1 :=
    congrArg (fun p : Sphere2 => p.1 0) hp
  have hy : hopfY (section (base X)).1 = hopfY X.1.1 :=
    congrArg (fun p : Sphere2 => p.1 1) hp
  have hz : hopfZ (section (base X)).1 = hopfZ X.1.1 :=
    congrArg (fun p : Sphere2 => p.1 2) hp
  exact KKHopfOrbit.same_hopf_implies_unit_rotation
    (section (base X)).1 X.1.1 (section (base X)).2 X.1.2 hx hy hz

noncomputable def phase (X : NorthTotal) : UnitPhase := by
  let N : X4 := (section (base X)).1
  let C : ℝ := KKHopfActionFree.dot4 N X.1.1
  let S : ℝ := KKHopfPhaseUnique.skew N X.1.1
  refine ⟨(fun i => if i=0 then C else S), ?_⟩
  obtain ⟨c,s,hunit,hrot⟩ := exists_rotation X
  have hc : C=c := by
    dsimp [C]
    rw [←hrot, KKHopfActionFree.dot_rotate, (section (base X)).2]
    ring
  have hs : S=s := by
    dsimp [S]
    rw [←hrot, KKHopfPhaseUnique.skew_rotate, (section (base X)).2]
    ring
  simpa [hc,hs] using hunit

theorem phase_reconstruct (X : NorthTotal) :
    rotate ((phase X).1 0) ((phase X).1 1) (section (base X)).1 = X.1.1 := by
  obtain ⟨c,s,hunit,hrot⟩ := exists_rotation X
  have hc : (phase X).1 0=c := by
    change KKHopfActionFree.dot4 (section (base X)).1 X.1.1=c
    rw [←hrot, KKHopfActionFree.dot_rotate, (section (base X)).2]
    ring
  have hs : (phase X).1 1=s := by
    change KKHopfPhaseUnique.skew (section (base X)).1 X.1.1=s
    rw [←hrot, KKHopfPhaseUnique.skew_rotate, (section (base X)).2]
    ring
  simpa [hc,hs] using hrot

noncomputable def rotatedSection (b : NorthBase) (p : UnitPhase) : Sphere3 := by
  refine ⟨rotate (p.1 0) (p.1 1) (section b).1, ?_⟩
  rw [radius_rotate, p.2, one_mul, (section b).2]

theorem proj_rotatedSection (b : NorthBase) (p : UnitPhase) :
    proj (rotatedSection b p) = b.1 := by
  calc
    proj (rotatedSection b p) = proj (section b) := by
      have hhopf := hopf_unit_circle_invariant
        (p.1 0) (p.1 1) (section b).1 p.2
      apply Subtype.ext
      funext i
      fin_cases i
      · change hopfX (rotate (p.1 0) (p.1 1) (section b).1) =
          hopfX (section b).1
        exact hhopf.1
      · change hopfY (rotate (p.1 0) (p.1 1) (section b).1) =
          hopfY (section b).1
        exact hhopf.2.1
      · change hopfZ (rotate (p.1 0) (p.1 1) (section b).1) =
          hopfZ (section b).1
        exact hhopf.2.2.1
    _ = b.1 := section_projects b

noncomputable def encode (b : NorthBase) (p : UnitPhase) : NorthTotal :=
  ⟨rotatedSection b p, by rw [proj_rotatedSection]; exact b.2⟩

noncomputable def decode (X : NorthTotal) : NorthBase × UnitPhase :=
  (base X, phase X)

theorem decode_encode (b : NorthBase) (p : UnitPhase) :
    decode (encode b p) = (b,p) := by
  have hb : base (encode b p) = b := by
    apply Subtype.ext
    exact proj_rotatedSection b p
  have hp : phase (encode b p) = p := by
    apply Subtype.ext
    funext i
    fin_cases i
    · change KKHopfActionFree.dot4 (section (base (encode b p))).1
          (encode b p).1.1 = p.1 0
      rw [hb]
      change KKHopfActionFree.dot4 (section b).1
        (rotate (p.1 0) (p.1 1) (section b).1) = p.1 0
      rw [KKHopfActionFree.dot_rotate, (section b).2]
      ring
    · change KKHopfPhaseUnique.skew (section (base (encode b p))).1
          (encode b p).1.1 = p.1 1
      rw [hb]
      change KKHopfPhaseUnique.skew (section b).1
        (rotate (p.1 0) (p.1 1) (section b).1) = p.1 1
      rw [KKHopfPhaseUnique.skew_rotate, (section b).2]
      ring
  simp [decode,hb,hp]

theorem encode_decode (X : NorthTotal) :
    encode (decode X).1 (decode X).2 = X := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  have h := congrArg (fun V : X4 => V i) (phase_reconstruct X)
  simpa [decode,encode] using h

/-- Explicit fibre chart: an actual algebraic equivalence, with no quotient shortcut. -/
noncomputable def northTrivialization : NorthTotal ≃ NorthBase × UnitPhase where
  toFun := decode
  invFun := fun bp => encode bp.1 bp.2
  left_inv := encode_decode
  right_inv := by intro bp; rcases bp with ⟨b,p⟩; exact decode_encode b p

end KKHopfNorthTriv
