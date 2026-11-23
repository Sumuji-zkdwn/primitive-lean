import SquareClock
import ObservedQuotient
import WeightedPI
import ProductPI
import HeightLaw
import RawGeometry
import RawFailure

/-! Integrated endpoint. The standard Laakso-times-circle PI and regularity are
the published analytic inputs. The sampled law, observed quotient, gate dynamics
and coordinate change in the conclusion are explicit. -/
noncomputable section
open MeasureTheory ObservedSandpile
open scoped ENNReal
namespace SingleSquare

abbrev StandardSpace := Quot (gate ternary) × Phase
abbrev FractalDim : ℝ := 2 + Real.log 2 / Real.log 3

def standardPoint (s : Samples) : StandardSpace := (Quot.mk _ s.1, s.2)
def representative (x : StandardSpace) : Samples := (x.1.out, x.2)

def standard : Observation Samples StandardSpace where
  law := standardLaw
  readout := standardPoint
  distance := fun x y =>
    (limitDistance (Equiv.refl H) (representative x) (representative y)).toReal
  borelTest := fun g => Measurable (g ∘ standardPoint)

/-- At every gate present in the quotient, a physical input at its birth level
realises its flip, preserves the circle, and has the prescribed minimal period. -/
def PhysicalGates (e : H ≃ H) : Prop :=
  ∀ (x : H) (k : ℕ), ternary (e x) k → ∃ j : ℕ, 0 < j ∧ j < 3^(k+1) ∧
    (e x).1 = 2*(j:ℝ)/3^(k+1)-1 ∧ ∀ s : SquareClock.Config,
      (∃ t, SquareClock.Inputs (3^(k+1)) j (3^(k+1)) s t) ∧
      (∀ r, 0 < r → r < 3^(k+1) → ∀ u, SquareClock.Inputs (3^(k+1)) j r s u →
        SquareClock.phase (3^(k+1)) u ≠ SquareClock.phase (3^(k+1)) s) ∧
      (∀ t, SquareClock.Inputs (3^(k+1)) j (3^(k+1)) s t →
        SquareClock.angle (3^(k+1)) t = SquareClock.angle (3^(k+1)) s ∧
        ∀ P, SquareClock.observedBit (3^(k+1)) P t =
          ((if 3^(k+1) = P then 1 else 0) + SquareClock.observedBit (3^(k+1)) P s)%2)

theorem physical_gates (e : H ≃ H) : PhysicalGates e := by
  rintro x k ⟨j,hj,hbound,hfresh,hx⟩
  refine ⟨j,hj,hbound,hx,?_⟩
  intro s
  have hp := SquareClock.fresh_period (k+1) j (by omega : j%3 ≠ 0)
  have H := SquareClock.sandpile_gate (m := k+1) ⟨hj,hbound⟩ s
  have A := SquareClock.square_phase_and_gate (m := k+1) ⟨hj,hbound⟩ s
  exact ⟨by simpa only [hp] using H.1, by simpa only [hp] using H.2.1,
    by simpa only [hp] using A.2.2.1⟩

def raw (a : ℝ) (ha : 0 < a) :
    Observation Samples (Raw.Point (powerCoordinate (a+1) (by linarith))) :=
  let p := a+1
  let hp : 0 < p := by dsimp [p]; linarith
  Raw.data (powerCoordinate p hp) standardLaw
    (fun w => (calibratedEquiv p hp).symm (standardPoint w))

theorem same_samples (a : ℝ) (ha : 0 < a) :
    let p := a+1
    let hp : 0 < p := by dsimp [p]; linarith
    (raw a ha).law = (reindex standard (calibratedEquiv p hp)).law ∧
    (raw a ha).readout = (reindex standard (calibratedEquiv p hp)).readout := ⟨rfl,rfl⟩

theorem raw_failure (a : ℝ) (ha : 0 < a) : ¬ WeakPI (raw a ha) := by
  let e := powerCoordinate (a+1) (by linarith : 0 < a+1)
  let D := raw a ha
  let h := fun x : Raw.Point e => (Raw.height e x).1
  have meas : Measurable (fun s => h (D.readout s)) := rawSampleHeight_measurable a ha.le
  have hB (ψ : ℝ → ℝ≥0∞) (hp : Measurable ψ) : D.borelTest (fun x => ψ (h x)) :=
    hp.comp meas
  letI : IsProbabilityMeasure D.law := standardLaw_probability
  obtain ⟨hl,hr⟩ := sample_wings a ha.le
  let x := D.readout ((⟨0,by constructor <;> norm_num⟩, fun _ => false),0)
  apply SubLaakso.RawFailure.no_PI_of_thin_band D h meas (Raw.height_control e) hB x
    (R:=5) (a:=a) (c:=1/4) (by norm_num) ha (by norm_num)
  · exact fun _ => Raw.diameter_bound e _ _
  · exact hl
  · exact hr
  · intro δ hδ hd
    exact (sample_band_mass a ha.le hδ hd).le

/-- Read the conclusion as a single construction at the same exponent a and
on the same measured sandpile observation, for every positive real a. -/
theorem single_square_realization (a : ℝ) (ha : 0 < a)
    (basePI : WeakPI standard) (baseRegular : Regular standard FractalDim) :
    let p := a+1
    let hp : 0 < p := by dsimp [p]; linarith
    let e := powerCoordinate p hp
    let D := reindex standard (calibratedEquiv p hp)
    PhysicalGates e ∧ (¬ Nonempty (Fibre ≃ₜ Bits)) ∧
    (raw a ha).law = D.law ∧ (raw a ha).readout = D.readout ∧
    (¬ WeakPI (raw a ha)) ∧ WeakPI D ∧ Regular D FractalDim ∧
    (∀ x y, limitDistance e x y =
      limitDistance (Equiv.refl H) (relabelFull e x) (relabelFull e y)) ∧
    (∀ u v : ℝ, (∫ x in u..v, p * |x|^a) = signedPower p v - signedPower p u) ∧
    ¬ (∃ C : ℝ, 0<C ∧ ∀ δ : ℝ, 0<δ → δ≤1/2 →
      SubLaakso.WFS.rampOsc a 0 δ ≤ C * SubLaakso.WFS.rampEnergy a 0 δ) := by
  dsimp only
  have h := calibrated_PI_and_regular (a+1) (by linarith) standard _ basePI baseRegular
  refine ⟨physical_gates _, h.2.2, rfl, rfl, raw_failure a ha, h.1, h.2.1, limitDistance_eq_standard _ _,
    fun u v => SubLaakso.WFS.calibrated_interval_mass ha.le u v, ?_⟩
  intro H
  exact (not_le.mpr ha) ((SubLaakso.WFS.ramp_test_PI_iff ha.le le_rfl).mp H)

#print axioms single_square_realization
#print axioms raw_failure
end SingleSquare
