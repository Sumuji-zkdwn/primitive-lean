import Research.SiphonPolynomialE
import Research.ElasticaObservationQuotient

/-!
# Predictive quotient of a polynomial automorphism

Reuses the explicit invertible E and invariant I from SiphonPolynomialE,
and the action-word equivalence and quotient from ElasticaObservationBridge.

The readout observes only the first coordinate. Under E, the complete
predictive signature is (u, I²); the sign of I is invisible for any number
of E-only observations. Adding the vertical translation R(u,v)=(u,v+1)
allows the three words [], [E], [R,E] to recover the whole state.

All claims are algebraic. The action R is a deliberately chosen probe, not
a measured or physically calibrated siphon update.
-/

namespace Elastica.SiphonPredictiveQuotient

open Elastica.SiphonPolynomialE
open ElasticaObservationBridge

abbrev State := ℝ × ℝ

/-- Public readout, which does not directly expose the invariant I. -/
def K (z : State) : ℝ := z.1

/-- The only action in the original alphabet. -/
def oldStep (_ : Unit) (z : State) : State := E z

/-- A new non-invariant-preserving probe. -/
def freshStep (_ : Unit) (z : State) : State := (z.1, z.2 + 1)

/-- Exact predictive compression of all E-only observation words. -/
def signature (z : State) : ℝ × ℝ := (K z, (I z) ^ 2)

/-- The descended dynamics on the compressed observer state. -/
def signatureStep (s : ℝ × ℝ) : ℝ × ℝ := (s.1 + s.2, s.2)

theorem readout_E (z : State) : K (E z) = K z + (I z) ^ 2 := rfl

theorem invariant_fresh (z : State) :
    I (freshStep () z) = I z + 1 := by
  dsimp [freshStep, I]
  ring

theorem readout_fresh_E (z : State) :
    K (E (freshStep () z)) = K z + (I z + 1) ^ 2 := by
  rw [readout_E, invariant_fresh]
  rfl

/-- Semiconjugacy: the polynomial dynamics induces a translation on signatures. -/
theorem signature_E (z : State) :
    signature (E z) = signatureStep (signature z) := by
  apply Prod.ext
  · exact readout_E z
  · change (I (E z)) ^ 2 = (I z) ^ 2
    rw [I_E]

private theorem signature_run_congr (word : List Unit) :
    ∀ z t : State, signature z = signature t →
      signature (run oldStep word z) = signature (run oldStep word t) := by
  induction word with
  | nil =>
      intro z t h
      simpa [run] using h
  | cons _ tail ih =>
      intro z t h
      change signature (run oldStep tail (E z)) =
        signature (run oldStep tail (E t))
      apply ih
      calc
        signature (E z) = signatureStep (signature z) := signature_E z
        _ = signatureStep (signature t) := congrArg signatureStep h
        _ = signature (E t) := (signature_E t).symm

/-- Two visible samples, at times 0 and 1, classify every E-only future. -/
theorem old_obs_iff_signature (z t : State) :
    ObsEq K oldStep z t ↔ signature z = signature t := by
  constructor
  · intro h
    have h0 : K z = K t := by
      simpa [run] using (h [])
    have h1 : K (E z) = K (E t) := by
      simpa [run, oldStep] using (h [()])
    rw [readout_E, readout_E] at h1
    apply Prod.ext
    · exact h0
    · change (I z) ^ 2 = (I t) ^ 2
      linarith
  · intro h word
    have hs := signature_run_congr word z t h
    exact congrArg Prod.fst hs

/-- The added probe breaks the residual sign ambiguity for all real states. -/
theorem extended_obs_iff_eq (z t : State) :
    ObsEq K (sumStep oldStep freshStep) z t ↔ z = t := by
  constructor
  · intro h
    have h0 : K z = K t := by
      simpa [run] using (h [])
    have h1 : K (E z) = K (E t) := by
      simpa only [run, sumStep, oldStep] using
        (h [Sum.inl ()])
    have h2 : K (E (freshStep () z)) =
        K (E (freshStep () t)) := by
      simpa only [run, sumStep, oldStep] using
        (h [Sum.inr (), Sum.inl ()])
    rw [readout_E, readout_E] at h1
    rw [readout_fresh_E, readout_fresh_E] at h2
    have hI : I z = I t := by
      nlinarith [h0, h1, h2]
    apply Prod.ext
    · exact h0
    · dsimp [I] at hI
      change z.1 = t.1 at h0
      rw [h0] at hI
      linarith
  · intro h
    subst t
    intro word
    rfl

/-- Every physical state now occupies its own predictive quotient class. -/
theorem extended_encode_injective :
    Function.Injective (encode K (sumStep oldStep freshStep)) := by
  intro z t h
  exact (extended_obs_iff_eq z t).mp
    ((encode_eq_iff K (sumStep oldStep freshStep) z t).mp h)

/-- Flip just the hidden sign I, without changing the first coordinate. -/
def mirror (z : State) : State := (z.1, -(I z) - z.1 ^ 3)

theorem invariant_mirror (z : State) : I (mirror z) = -(I z) := by
  dsimp [I, mirror]
  ring

theorem signature_mirror (z : State) : signature (mirror z) = signature z := by
  apply Prod.ext
  · rfl
  · change (I (mirror z)) ^ 2 = (I z) ^ 2
    rw [invariant_mirror]
    ring

theorem mirror_involutive (z : State) : mirror (mirror z) = z := by
  apply Prod.ext
  · rfl
  · change -(I (mirror z)) - (mirror z).1 ^ 3 = z.2
    rw [invariant_mirror]
    change I z - z.1 ^ 3 = z.2
    dsimp [I]
    ring

private theorem mirror_ne_of_invariant_nonzero (z : State)
    (hz : I z ≠ 0) : mirror z ≠ z := by
  intro h
  have hi := congrArg I h
  rw [invariant_mirror] at hi
  have hzero : I z = 0 := by linarith
  exact hz hzero

/-- The old quotient identifies z and mirror z, for every z. -/
theorem old_cannot_see_mirror (z : State) :
    ObsEq K oldStep z (mirror z) :=
  (old_obs_iff_signature z (mirror z)).mpr (signature_mirror z).symm

/-- Every nonzero hidden-sign pair is split by the added action alphabet. -/
theorem nonzero_mirror_quotient_split (z : State) (hz : I z ≠ 0) :
    ∃ q r : PredState K (sumStep oldStep freshStep),
      q ≠ r ∧ forget K oldStep freshStep q =
        forget K oldStep freshStep r := by
  have hnew : ¬ ObsEq K (sumStep oldStep freshStep) z (mirror z) := by
    intro h
    have heq := (extended_obs_iff_eq z (mirror z)).mp h
    exact (mirror_ne_of_invariant_nonzero z hz) heq.symm
  exact strict_refinement_splits_quotient K oldStep freshStep z (mirror z)
    (old_cannot_see_mirror z) hnew

#print axioms signature_E
#print axioms old_obs_iff_signature
#print axioms extended_obs_iff_eq
#print axioms extended_encode_injective
#print axioms nonzero_mirror_quotient_split

end Elastica.SiphonPredictiveQuotient
