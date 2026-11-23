import Mathlib.Tactic
import Research.KKHopfOrbit
import Research.KKHopfSurjective

/-!
# The Hopf orbit quotient is set-theoretically equivalent to S²

This is a bijection of types, not yet a homeomorphism or diffeomorphism.
The fibre relation used for Quotient is equality of Hopf images, and
fibre_iff_unit_orbit identifies it with the actual diagonal U(1) orbits
using the parent theorem KKHopfOrbit.same_hopf_iff_circle_orbit.
The explicit local section proves the image is the entire S².
-/
namespace KKHopfQuotient
open KKHopfGlobalAlgebra

abbrev Sphere3 := {X : X4 // radiusSq X = 1}
abbrev Sphere2 := {p : Fin 3 → ℝ // p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 = 1}

def proj (X : Sphere3) : Sphere2 := by
  refine ⟨(fun i => if i=0 then hopfX X.1
                  else if i=1 then hopfY X.1 else hopfZ X.1), ?_⟩
  change (hopfX X.1)^2 + (hopfY X.1)^2 + (hopfZ X.1)^2 = 1
  rw [hopf_norm, X.2]
  norm_num

/-- Every point of S² has an explicit preimage in S³. -/
theorem proj_surjective : Function.Surjective proj := by
  rintro ⟨b,hb⟩
  obtain ⟨X,hX,hx,hy,hz⟩ :=
    KKHopfSurjective.hopf_surjective_on_unit_spheres (b 0) (b 1) (b 2) hb
  refine ⟨⟨X,hX⟩, ?_⟩
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [proj,hx,hy,hz]

/-- Equating points whose Hopf images agree. By the parent theorem,
this is equivalently the actual diagonal free U(1) orbit relation. -/
def fibreSetoid : Setoid Sphere3 where
  r X Y := proj X = proj Y
  iseqv := ⟨by intro X; rfl,
            by intro X Y h; exact h.symm,
            by intro X Y Z h1 h2; exact h1.trans h2⟩

theorem fibre_iff_unit_orbit (X Y : Sphere3) :
    fibreSetoid.Rel X Y ↔
      ∃ C S : ℝ, C^2+S^2=1 ∧ rotate C S X.1=Y.1 := by
  have hiff := KKHopfOrbit.same_hopf_iff_circle_orbit X.1 Y.1 X.2 Y.2
  constructor
  · intro h
    have hx : hopfX X.1 = hopfX Y.1 :=
      congrArg (fun p : Sphere2 => p.1 0) h
    have hy : hopfY X.1 = hopfY Y.1 :=
      congrArg (fun p : Sphere2 => p.1 1) h
    have hz : hopfZ X.1 = hopfZ Y.1 :=
      congrArg (fun p : Sphere2 => p.1 2) h
    exact hiff.mp ⟨hx,hy,hz⟩
  · intro h
    obtain ⟨hx,hy,hz⟩ := hiff.mpr h
    change proj X = proj Y
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [proj,hx,hy,hz]

abbrev OrbitSpace := Quotient fibreSetoid

noncomputable def descent : OrbitSpace → Sphere2 :=
  Quotient.lift proj (by intro X Y h; exact h)

/-- On the level of sets, the quotient by the U(1) action is exactly S².
No topological/smooth manifold structure is inferred from this equivalence. -/
theorem descent_bijective : Function.Bijective descent := by
  constructor
  · intro Q R h
    obtain ⟨X,hX⟩ := Quotient.exists_rep Q
    obtain ⟨Y,hY⟩ := Quotient.exists_rep R
    rw [←hX, ←hY] at h ⊢
    change proj X = proj Y at h
    exact Quotient.sound h
  · intro b
    obtain ⟨X,hX⟩ := proj_surjective b
    refine ⟨Quotient.mk fibreSetoid X, ?_⟩
    simpa [descent] using hX

noncomputable def orbitEquivS2 : OrbitSpace ≃ Sphere2 :=
  Equiv.ofBijective descent descent_bijective

end KKHopfQuotient
