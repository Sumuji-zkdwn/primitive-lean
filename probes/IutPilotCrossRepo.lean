/-!
# Cross-repository specialization: primitive-lean × LANA iut
Generated compilation unit:
  import Mathlib
  import Iut.WallEquiv.Basic
  [verbatim contents of PilotVolumeTransport.inc]
  [this source]

The following is a genuine *typed* combination of both repositories. It
reuses a primitive-lean theorem in the LANA InitialThetaData/Ind3 domain.
The result is an equivalence, not an unconditional proof of SSIneq/abc.
-/

namespace PrimitiveIutCrossRepo

open Iut Iut.Wall

noncomputable section

/-- Specialize the proven abstract neutral-transport comparison criterion
to the actual LANA admissible region type, q-pilot arithmetic degree and
procession-normalized log-volume. This does NOT supply an SSIneq proof. -/
theorem pilot_window_iff_ss (D : InitialThetaData.{0}) :
    (∃ S : Ind3 D,
       -(sFactor (nC D) * D.qPilot.absLogQ) + logVol D S.1 =
         -D.qPilot.absLogQ) ↔ SSIneq D := by
  have hcomplete :
      ∀ v : ℝ, v ≤ logVol D (hullOf D (vcI D)) →
        ∃ S : Ind3 D, logVol D S.1 = v := by
    intro v hv
    exact (exists_ind3_logVol_iff D v).mpr hv
  have hh := LinearInputPilotTransport.neutral_transport_wall_iff
    D.qPilot.absLogQ (sFactor (nC D))
    (logVol D (hullOf D (vcI D)))
    (fun S : Ind3 D => logVol D S.1)
    (fun (_ : Unit) (S : Ind3 D) => S)
    (fun (_ : Unit) => (0 : ℝ))
    (⟨()⟩ : Nonempty Unit)
    (by intro g S; simp)
    (by intro g; rfl)
    (logVol_le_vcI D)
    hcomplete
  unfold SSIneq
  constructor
  · intro h
    apply hh.mp
    rcases h with ⟨S, hS⟩
    exact ⟨(), S, hS⟩
  · intro h
    rcases hh.mpr h with ⟨_, S, hS⟩
    exact ⟨S, hS⟩

/-- The same specialized bridge matches the LANA literal 9-1 predicate
for a chosen family of Hodge theaters, by an existing LANA equivalence. -/
theorem pilot_window_iff_lana91 (D : InitialThetaData.{0})
    {σ : Type} [Nonempty σ] (H : σ → HodgeTheater.ThetaPmEllNFHT D) :
    (∃ S : Ind3 D,
       -(sFactor (nC D) * D.qPilot.absLogQ) + logVol D S.1 =
         -D.qPilot.absLogQ) ↔ WallEquiv.Lana91 D H := by
  exact (pilot_window_iff_ss D).trans (WallEquiv.lana91_iff_ss H).symm

/-- A conditional route to the Corollary 3.12 numerical variant.
The missing arithmetic witness is *explicitly* a hypothesis. -/
theorem pilot_window_implies_cor312_variant (D : InitialThetaData.{0})
    (hw : ∃ S : Ind3 D,
       -(sFactor (nC D) * D.qPilot.absLogQ) + logVol D S.1 =
         -D.qPilot.absLogQ) :
    Corollary312Variant (concreteVariantData D) := by
  exact WallEquiv.variant_of_ss ((pilot_window_iff_ss D).mp hw)

end PrimitiveIutCrossRepo

#print axioms PrimitiveIutCrossRepo.pilot_window_iff_ss
#print axioms PrimitiveIutCrossRepo.pilot_window_iff_lana91
#print axioms PrimitiveIutCrossRepo.pilot_window_implies_cor312_variant
