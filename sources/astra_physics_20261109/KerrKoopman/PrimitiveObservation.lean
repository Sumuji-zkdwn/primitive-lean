import KerrKoopman.PrimitiveSource
import KerrKoopman.Reconstruction

/-!
# Primitive observations specialized to Kerr initial fields

The original primitive-lean observation identities are applied to the actual
smooth periodic, equal-energy family from `Reconstruction`. The probe is a
mathematical observable `energy - input * magneticValue`; no physical measuring
device, trajectory, or complete Koopman spectrum is inferred from it.
-/

open MeasureTheory

namespace KerrKoopman.PrimitiveObservation

noncomputable section

/-- Magnetic field in the smooth fixed-energy initial-data family. -/
def magnetic (ε Hbar : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Hbar + Reconstruction.profile ε n x

/-- Actual spatial mean of the Kerr density, with initial electric field one. -/
def initialEnergy (ε Hbar : ℝ) (n : ℕ) : ℝ :=
  (∫ x in (0 : ℝ)..(2 * Real.pi),
    magnetic ε Hbar n x ^ 2 / 2 + (1 : ℝ) / 2 + (1 : ℝ) / 4) /
      (2 * Real.pi)

/-- A primitive linear-input observable of the physical mean energy and H(0). -/
def probe (ε Hbar u : ℝ) (n : ℕ) : ℝ :=
  LinearInputObservation.energy (initialEnergy ε Hbar)
    (fun n => magnetic ε Hbar n 0) u n

theorem initialEnergy_eq (ε Hbar : ℝ) (hε : 0 ≤ ε) (n : ℕ) :
    initialEnergy ε Hbar n = Hbar ^ 2 / 2 + ε + 3 / 4 := by
  exact Reconstruction.kerr_initial_mean_energy ε hε n Hbar

/-- Applying primitive's two-input identity recovers the actual magnetic value. -/
theorem two_inputs_recover_magnetic (ε Hbar u v : ℝ) (huv : u ≠ v) (n : ℕ) :
    (probe ε Hbar u n - probe ε Hbar v n) / (v - u) =
      magnetic ε Hbar n 0 := by
  exact LinearInputObservation.recover_coordinate (initialEnergy ε Hbar)
    (fun n => magnetic ε Hbar n 0) u v huv n

/-- The same specialization retains the original quantitative noise estimate. -/
theorem magnetic_recovery_error_bound (ε Hbar u v : ℝ) (huv : u ≠ v) (n : ℕ)
    (errorU errorV epsU epsV : ℝ)
    (hU : |errorU| ≤ epsU) (hV : |errorV| ≤ epsV) :
    |((probe ε Hbar u n + errorU) - (probe ε Hbar v n + errorV)) / (v - u)
      - magnetic ε Hbar n 0| ≤ (epsU + epsV) / |v - u| := by
  exact LinearInputObservation.recovery_error_bound (initialEnergy ε Hbar)
    (fun n => magnetic ε Hbar n 0) u v huv n errorU errorV epsU epsV hU hV

/-- A common summary for every probe must retain the magnetic point value. -/
theorem probe_summary_decodes_magnetic {Q : Type*} (ε Hbar : ℝ)
    (encode : ℕ → Q) (decode : ℝ → Q → ℝ)
    (hdecode : ∀ u n, decode u (encode n) = probe ε Hbar u n) :
    ∃ magneticDecode : Q → ℝ,
      ∀ n, magneticDecode (encode n) = magnetic ε Hbar n 0 := by
  obtain ⟨pairDecode, hpair⟩ :=
    LinearInputObservation.summary_decodes_pair (initialEnergy ε Hbar)
      (fun n => magnetic ε Hbar n 0) encode decode hdecode
  exact ⟨fun q => (pairDecode q).2, fun n => congrArg Prod.snd (hpair n)⟩

/-- The conserved energy alone cannot supply all these observations, even
through an arbitrary nonlinear decoder. This concerns the scalar energy;
it does not discard the user's allowed full initial waveform. -/
theorem no_energy_only_probe_decoder (ε Hbar : ℝ) (hε : 0 < ε) :
    ¬ ∃ decode : ℝ → ℝ → ℝ,
      ∀ u n, decode u (initialEnergy ε Hbar n) = probe ε Hbar u n := by
  rintro ⟨decode, hdecode⟩
  obtain ⟨magneticDecode, hmagnetic⟩ := probe_summary_decodes_magnetic ε Hbar
    (initialEnergy ε Hbar) decode hdecode
  apply Reconstruction.no_uniform_peak_bound ε hε
  refine ⟨magneticDecode (Hbar ^ 2 / 2 + ε + 3 / 4) - Hbar, ?_⟩
  intro n
  have hn := hmagnetic n
  rw [initialEnergy_eq ε Hbar hε.le n] at hn
  change magneticDecode (Hbar ^ 2 / 2 + ε + 3 / 4) =
    Hbar + Reconstruction.profile ε n 0 at hn
  rw [Reconstruction.profile_zero] at hn
  linarith

/-- Two bounded linear probe decoders would produce the forbidden bounded
magnetic decoder. The space and encoding are shared by the whole family. -/
theorem no_bounded_two_probe_encoder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ε Hbar : ℝ) (hε : 0 < ε) (u v : ℝ) (huv : u ≠ v)
    (encode : ℕ → E) (decodeU decodeV : E →L[ℝ] ℝ)
    (B : ℝ) (hencode : ∀ n, ‖encode n‖ ≤ B) :
    ¬ ((∀ n, decodeU (encode n) = probe ε Hbar u n) ∧
       (∀ n, decodeV (encode n) = probe ε Hbar v n)) := by
  rintro ⟨hU, hV⟩
  let magneticDecode : E →L[ℝ] ℝ := (v - u)⁻¹ • (decodeU - decodeV)
  apply Reconstruction.no_bounded_magnetic_encoder ε hε Hbar
    encode magneticDecode B hencode
  intro n
  change (v - u)⁻¹ * (decodeU (encode n) - decodeV (encode n)) = _
  rw [hU n, hV n]
  simpa only [div_eq_mul_inv, mul_comm] using
    two_inputs_recover_magnetic ε Hbar u v huv n

/-- Eigenfunction pullback from primitive extends to every discrete iterate.
This assumes a semiconjugacy and an actual reduced eigenfunction; it does not
construct either or assert spectral completeness. -/
theorem eigenfunction_pullback_iterate {S Q : Type*}
    (f : S → S) (g : Q → Q) (q : S → Q)
    (h : ∀ s, q (f s) = g (q s))
    (psi : Q → ℝ) (lam : ℝ) (hp : ∀ z, psi (g z) = lam * psi z)
    (n : ℕ) (s : S) :
    psi (q (f^[n] s)) = lam ^ n * psi (q s) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rw [LinearInputKoopmanDescent.eigenfunction_pullback f g q h psi lam hp]
      rw [ih, pow_succ]
      ring

/-- Surjectivity prevents a nonzero reduced eigenfunction from vanishing
identically after pullback. The iterate law is then nontrivial at some state. -/
theorem nontrivial_eigenfunction_pullback {S Q : Type*}
    (f : S → S) (g : Q → Q) (q : S → Q)
    (h : ∀ s, q (f s) = g (q s)) (hq : Function.Surjective q)
    (psi : Q → ℝ) (lam : ℝ) (hp : ∀ z, psi (g z) = lam * psi z)
    (hne : ∃ z, psi z ≠ 0) :
    ∃ s, psi (q s) ≠ 0 ∧
      ∀ n : ℕ, psi (q (f^[n] s)) = lam ^ n * psi (q s) := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨s, hs⟩ := hq z
  refine ⟨s, ?_, fun n => eigenfunction_pullback_iterate f g q h psi lam hp n s⟩
  simpa only [hs] using hz

/-- The reduced map transported through one reversible scale, shared by all
initial states. No continuity or boundedness is asserted by this definition. -/
def scaledStep {Q R : Type*} (scale : Q ≃ R) (g : Q → Q) (r : R) : R :=
  scale (g (scale.symm r))

def scaledObservable {Q R : Type*} (scale : Q ≃ R) (psi : Q → ℝ) (r : R) : ℝ :=
  psi (scale.symm r)

theorem shared_scale_semiconjugacy {S Q R : Type*}
    (f : S → S) (g : Q → Q) (q : S → Q)
    (h : ∀ s, q (f s) = g (q s)) (scale : Q ≃ R) (s : S) :
    scale (q (f s)) = scaledStep scale g (scale (q s)) := by
  simp only [scaledStep, Equiv.symm_apply_apply, h]

theorem shared_scale_eigenfunction {Q R : Type*}
    (g : Q → Q) (psi : Q → ℝ) (lam : ℝ)
    (hp : ∀ z, psi (g z) = lam * psi z) (scale : Q ≃ R) (r : R) :
    scaledObservable scale psi (scaledStep scale g r) =
      lam * scaledObservable scale psi r := by
  simp only [scaledObservable, scaledStep, Equiv.symm_apply_apply, hp]

/-- A reversible shared scale preserves the exact iterate formula through
primitive's semiconjugacy theorem. It does not supply missing eigenfunctions,
reconstruction, convergence, or a physical evolution in the first place. -/
theorem scaled_eigenfunction_pullback_iterate {S Q R : Type*}
    (f : S → S) (g : Q → Q) (q : S → Q)
    (h : ∀ s, q (f s) = g (q s))
    (psi : Q → ℝ) (lam : ℝ) (hp : ∀ z, psi (g z) = lam * psi z)
    (scale : Q ≃ R) (n : ℕ) (s : S) :
    scaledObservable scale psi (scale (q (f^[n] s))) =
      lam ^ n * scaledObservable scale psi (scale (q s)) := by
  exact eigenfunction_pullback_iterate f (scaledStep scale g)
    (fun s => scale (q s)) (shared_scale_semiconjugacy f g q h scale)
    (scaledObservable scale psi) lam
    (shared_scale_eigenfunction g psi lam hp scale) n s

end

end KerrKoopman.PrimitiveObservation
