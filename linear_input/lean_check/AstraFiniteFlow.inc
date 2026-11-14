/-!
# The actual finite Kerr system: global flow and convergent explicit splitting

Every finite real matrix is realized as a bounded operator on Euclidean space.
The nonlinear map is the previously proved Kerr material inverse, componentwise.
The common coordinate equivalence identifies the old finite shear update exactly.
No skewness assumption is needed for existence, uniqueness, or convergence.
-/

namespace KerrKoopman.FiniteFlow

noncomputable section

open scoped Topology

variable {ι : Type*} [Fintype ι]

abbrev Vector (ι : Type*) := EuclideanSpace ℝ ι
abbrev State (ι : Type*) := HilbertShear.State (Vector ι)

/-- The coordinate equivalence is fixed for the finite index set, not the initial data. -/
def coordinates : State ι ≃L[ℝ] ExactShear.State ι :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (Vector ι) (Vector ι)).trans
    ((EuclideanSpace.equiv ι ℝ).prodCongr (EuclideanSpace.equiv ι ℝ))

def encode (z : ExactShear.State ι) : State ι := coordinates.symm z
def decode (z : State ι) : ExactShear.State ι := coordinates z

omit [Fintype ι] in
theorem decode_encode (z : ExactShear.State ι) : decode (encode z) = z :=
  coordinates.apply_symm_apply z

omit [Fintype ι] in
theorem encode_decode (z : State ι) : encode (decode z) = z :=
  coordinates.symm_apply_apply z

theorem encode_norm_sq (z : ExactShear.State ι) :
    ‖encode z‖ ^ 2 = (∑ i, (z.1 i) ^ 2) + ∑ i, (z.2 i) ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq]
  rfl

def matrixLinear (Q : ι → ι → ℝ) : Vector ι →ₗ[ℝ] Vector ι where
  toFun x := WithLp.toLp 2 (fun i => ∑ j, Q i j * x j)
  map_add' x y := by
    ext i
    change (∑ j, Q i j * (x j + y j)) = (∑ j, Q i j * x j) + ∑ j, Q i j * y j
    simp only [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext i
    change (∑ j, Q i j * (c * x j)) = c * ∑ j, Q i j * x j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

def matrixOp (Q : ι → ι → ℝ) : Vector ι →L[ℝ] Vector ι :=
  (matrixLinear Q).toContinuousLinearMap

theorem matrixOp_apply (Q : ι → ι → ℝ) (x : Vector ι) (i : ι) :
    matrixOp Q x i = FiniteEnergy.applyQ Q (fun j => x j) i := rfl

def material (x : Vector ι) : Vector ι :=
  WithLp.toLp 2 (fun i => PrimitiveConstitutive.materialInverse (x i))

theorem material_lipschitz : LipschitzWith 1 (material : Vector ι → Vector ι) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_one, one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  change |PrimitiveConstitutive.materialInverse (x i) -
    PrimitiveConstitutive.materialInverse (y i)| ^ 2 ≤ |x i - y i| ^ 2
  exact (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr
    (PrimitiveConstitutive.materialInverse_stability (x i) (y i))

omit [Fintype ι] in
theorem material_zero : material (0 : Vector ι) = 0 := by
  ext i
  change PrimitiveConstitutive.materialInverse 0 = 0
  simpa only [Riccati.constitutive, zero_pow (by decide : (3 : ℕ) ≠ 0),
    zero_div, add_zero] using PrimitiveConstitutive.materialInverse_constitutive 0

def vectorField (Q : ι → ι → ℝ) : State ι → State ι :=
  HilbertShear.field (matrixOp Q) material

def step (Q : ι → ι → ℝ) (t : ℝ) : State ι → State ι :=
  HilbertShear.lieStep (matrixOp Q) material t

theorem encode_lieStep (Q : ι → ι → ℝ) (t : ℝ) (z : ExactShear.State ι) :
    encode (ExactShear.lieStep Q t z) = step Q t (encode z) := rfl

theorem encode_iterate (Q : ι → ι → ℝ) (t : ℝ) (n : ℕ) (z : ExactShear.State ι) :
    encode ((ExactShear.lieStep Q t)^[n] z) = (step Q t)^[n] (encode z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', encode_lieStep, ih,
        Function.iterate_succ_apply']

def flow (Q : ι → ι → ℝ) (t : ℝ) : State ι → State ι :=
  HilbertFlow.flow (matrixOp Q) material material_lipschitz t

theorem flow_zero (Q : ι → ι → ℝ) (z : State ι) : flow Q 0 z = z :=
  HilbertFlow.flow_zero _ _ _ _

theorem hasDerivAt_flow (Q : ι → ι → ℝ) (t : ℝ) (z : State ι) :
    HasDerivAt (fun s => flow Q s z) (vectorField Q (flow Q t z)) t :=
  HilbertFlow.hasDerivAt_flow _ _ _ _ _

theorem exists_global (Q : ι → ι → ℝ) (z : State ι) :
    ∃ u : ℝ → State ι, u 0 = z ∧ ∀ t, HasDerivAt u (vectorField Q (u t)) t :=
  ⟨fun t => flow Q t z, flow_zero Q z, fun t => hasDerivAt_flow Q t z⟩

theorem global_unique (Q : ι → ι → ℝ) {u v : ℝ → State ι}
    (hu : ∀ t, HasDerivAt u (vectorField Q (u t)) t)
    (hv : ∀ t, HasDerivAt v (vectorField Q (v t)) t) (h₀ : u 0 = v 0) : u = v :=
  HilbertFlow.global_unique (HilbertShear.field_lipschitz (matrixOp Q) material
    material_lipschitz) hu hv h₀

theorem flow_add (Q : ι → ι → ℝ) (t s : ℝ) (z : State ι) :
    flow Q (t + s) z = flow Q t (flow Q s z) :=
  HilbertFlow.flow_add _ _ _ _ _ _

theorem flow_inverse (Q : ι → ι → ℝ) (t : ℝ) (z : State ι) :
    flow Q (-t) (flow Q t z) = z := by
  rw [← flow_add, neg_add_cancel, flow_zero]

theorem finite_time_error_le (Q : ι → ι → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (z : State ι) (n : ℕ) (hn : 0 < n) :
    ‖(step Q (T / n))^[n] z - flow Q T z‖ ≤
      ((3 / 2 : ℝ) * ‖matrixOp Q‖ ^ 2 * T ^ 2 * ‖z‖ / n) *
        Real.exp (‖matrixOp Q‖ * T) :=
  HilbertIteration.finite_time_error_le (matrixOp Q) material material_lipschitz
    material_zero T hT z n hn

theorem iterate_tendsto_flow (Q : ι → ι → ℝ) (T : ℝ) (hT : 0 ≤ T) (z : State ι) :
    Filter.Tendsto (fun n : ℕ => (step Q (T / n))^[n] z)
      Filter.atTop (𝓝 (flow Q T z)) :=
  HilbertIteration.iterate_tendsto_flow (matrixOp Q) material material_lipschitz
    material_zero T hT z

/-- The same flow written in the original finite displacement/magnetic arrays. -/
def rawFlow (Q : ι → ι → ℝ) (t : ℝ) (z : ExactShear.State ι) : ExactShear.State ι :=
  decode (flow Q t (encode z))

def rawVectorField (Q : ι → ι → ℝ) (z : ExactShear.State ι) : ExactShear.State ι :=
  decode (vectorField Q (encode z))

theorem rawVectorField_formula (Q : ι → ι → ℝ) (z : ExactShear.State ι) :
    rawVectorField Q z =
      (fun i => -FiniteEnergy.applyQ Q z.2 i,
       fun i => -FiniteEnergy.applyQ Q (ExactShear.fieldE z.1) i) := rfl

theorem hasDerivAt_rawFlow (Q : ι → ι → ℝ) (t : ℝ) (z : ExactShear.State ι) :
    HasDerivAt (fun s => rawFlow Q s z) (rawVectorField Q (rawFlow Q t z)) t := by
  have h := coordinates.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_flow Q t (encode z))
  change HasDerivAt (fun s => rawFlow Q s z)
    (decode (vectorField Q (flow Q t (encode z)))) t at h
  simpa only [rawVectorField, rawFlow, encode_decode] using h

theorem rawFlow_zero (Q : ι → ι → ℝ) (z : ExactShear.State ι) : rawFlow Q 0 z = z := by
  rw [rawFlow, flow_zero, decode_encode]

theorem exists_global_raw (Q : ι → ι → ℝ) (z : ExactShear.State ι) :
    ∃ u : ℝ → ExactShear.State ι, u 0 = z ∧
      ∀ t, HasDerivAt u (rawVectorField Q (u t)) t :=
  ⟨fun t => rawFlow Q t z, rawFlow_zero Q z, fun t => hasDerivAt_rawFlow Q t z⟩

theorem raw_global_unique (Q : ι → ι → ℝ) {u v : ℝ → ExactShear.State ι}
    (hu : ∀ t, HasDerivAt u (rawVectorField Q (u t)) t)
    (hv : ∀ t, HasDerivAt v (rawVectorField Q (v t)) t) (h₀ : u 0 = v 0) : u = v := by
  have hu' (t : ℝ) : HasDerivAt (fun s => encode (u s))
      (vectorField Q (encode (u t))) t := by
    have h := coordinates.symm.hasFDerivAt.comp_hasDerivAt t (hu t)
    change HasDerivAt (fun s => encode (u s)) (encode (rawVectorField Q (u t))) t at h
    simpa only [rawVectorField, encode_decode] using h
  have hv' (t : ℝ) : HasDerivAt (fun s => encode (v s))
      (vectorField Q (encode (v t))) t := by
    have h := coordinates.symm.hasFDerivAt.comp_hasDerivAt t (hv t)
    change HasDerivAt (fun s => encode (v s)) (encode (rawVectorField Q (v t))) t at h
    simpa only [rawVectorField, encode_decode] using h
  have heq := global_unique Q hu' hv' (congrArg encode h₀)
  funext t
  exact coordinates.symm.injective (congrFun heq t)

theorem rawFlow_add (Q : ι → ι → ℝ) (t s : ℝ) (z : ExactShear.State ι) :
    rawFlow Q (t + s) z = rawFlow Q t (rawFlow Q s z) := by
  simp only [rawFlow, encode_decode, flow_add]

theorem original_finite_time_error_le (Q : ι → ι → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (z : ExactShear.State ι) (n : ℕ) (hn : 0 < n) :
    ‖encode ((ExactShear.lieStep Q (T / n))^[n] z) - encode (rawFlow Q T z)‖ ≤
      ((3 / 2 : ℝ) * ‖matrixOp Q‖ ^ 2 * T ^ 2 * ‖encode z‖ / n) *
        Real.exp (‖matrixOp Q‖ * T) := by
  rw [encode_iterate, rawFlow, encode_decode]
  exact finite_time_error_le Q T hT (encode z) n hn

theorem original_iterate_tendsto_flow (Q : ι → ι → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (z : ExactShear.State ι) :
    Filter.Tendsto (fun n : ℕ => (ExactShear.lieStep Q (T / n))^[n] z)
      Filter.atTop (𝓝 (rawFlow Q T z)) := by
  have h := (coordinates.continuous.tendsto (flow Q T (encode z))).comp
    (iterate_tendsto_flow Q T hT (encode z))
  have heq (n : ℕ) : decode ((step Q (T / n))^[n] (encode z)) =
      (ExactShear.lieStep Q (T / n))^[n] z := by
    rw [← encode_iterate, decode_encode]
  change Filter.Tendsto (fun n : ℕ => decode ((step Q (T / n))^[n] (encode z)))
    Filter.atTop (𝓝 (rawFlow Q T z)) at h
  simpa only [heq] using h

def displacementCoordinate (i : ι) : State ι →L[ℝ] ℝ where
  toFun z := z.fst i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

def magneticCoordinate (i : ι) : State ι →L[ℝ] ℝ where
  toFun z := z.snd i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

def electric (z : State ι) (i : ι) : ℝ := PrimitiveConstitutive.materialInverse (z.fst i)

omit [Fintype ι] in
theorem constitutive_electric (z : State ι) (i : ι) :
    Riccati.constitutive (electric z i) = z.fst i :=
  PrimitiveConstitutive.constitutive_materialInverse _

theorem hasDerivAt_displacement (Q : ι → ι → ℝ) (t : ℝ) (z : State ι) (i : ι) :
    HasDerivAt (fun s => (flow Q s z).fst i)
      (-FiniteEnergy.applyQ Q (fun j => (flow Q t z).snd j) i) t :=
  (displacementCoordinate i).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_flow Q t z)

theorem hasDerivAt_magnetic (Q : ι → ι → ℝ) (t : ℝ) (z : State ι) (i : ι) :
    HasDerivAt (fun s => (flow Q s z).snd i)
      (FiniteEnergy.magneticRate Q (electric (flow Q t z)) i) t :=
  (magneticCoordinate i).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_flow Q t z)

theorem hasDerivAt_electric (Q : ι → ι → ℝ) (t : ℝ) (z : State ι) (i : ι) :
    HasDerivAt (fun s => electric (flow Q s z) i)
      (FiniteEnergy.electricRate Q (electric (flow Q t z))
        (fun j => (flow Q t z).snd j) i) t := by
  have h := (ExplicitMaterial.hasDerivAt_materialInverse ((flow Q t z).fst i)).comp t
    (hasDerivAt_displacement Q t z i)
  convert h using 1
  · rfl
  · dsimp only [FiniteEnergy.electricRate, electric]
    ring

/-- The constructed flow, rather than an assumed trajectory, satisfies the physical ODEs. -/
theorem restored_physical_equations (Q : ι → ι → ℝ) (z : State ι) (t : ℝ) (i : ι) :
    HasDerivAt (fun s => electric (flow Q s z) i)
      (FiniteEnergy.electricRate Q (electric (flow Q t z))
        (fun j => (flow Q t z).snd j) i) t ∧
    HasDerivAt (fun s => (flow Q s z).snd i)
      (FiniteEnergy.magneticRate Q (electric (flow Q t z)) i) t :=
  ⟨hasDerivAt_electric Q t z i, hasDerivAt_magnetic Q t z i⟩

/-- Skewness is required here, but not for global existence or the splitting limit. -/
theorem energy_conserved (Q : ι → ι → ℝ) (hQ : ∀ i j, Q i j = -Q j i)
    (z : State ι) (t t₀ : ℝ) :
    FiniteEnergy.energy (electric (flow Q t z)) (fun i => (flow Q t z).snd i) =
      FiniteEnergy.energy (electric (flow Q t₀ z)) (fun i => (flow Q t₀ z).snd i) :=
  FiniteEnergy.energy_conserved Q hQ (fun s => electric (flow Q s z))
    (fun s i => (flow Q s z).snd i) (fun s i => hasDerivAt_electric Q s z i)
    (fun s i => hasDerivAt_magnetic Q s z i) t t₀

/-- Restore physical (E,H) in the same Euclidean product norm. -/
def restore (z : State ι) : State ι := WithLp.toLp 2 (material z.fst, z.snd)

theorem restore_norm_sub_le (z w : State ι) : ‖restore z - restore w‖ ≤ ‖z - w‖ := by
  have hf : ‖material z.fst - material w.fst‖ ≤ ‖z.fst - w.fst‖ := by
    simpa only [NNReal.coe_one, one_mul] using material_lipschitz.norm_sub_le z.fst w.fst
  have hf2 : ‖material z.fst - material w.fst‖ ^ 2 ≤ ‖z.fst - w.fst‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hf
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  change ‖material z.fst - material w.fst‖ ^ 2 + ‖z.snd - w.snd‖ ^ 2 ≤
    ‖z.fst - w.fst‖ ^ 2 + ‖z.snd - w.snd‖ ^ 2
  linarith

theorem restore_lipschitz : LipschitzWith 1 (restore : State ι → State ι) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using restore_norm_sub_le z w

theorem restored_finite_time_error_le (Q : ι → ι → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (z : State ι) (n : ℕ) (hn : 0 < n) :
    ‖restore ((step Q (T / n))^[n] z) - restore (flow Q T z)‖ ≤
      ((3 / 2 : ℝ) * ‖matrixOp Q‖ ^ 2 * T ^ 2 * ‖z‖ / n) *
        Real.exp (‖matrixOp Q‖ * T) :=
  (restore_norm_sub_le _ _).trans (finite_time_error_le Q T hT z n hn)

theorem restored_iterate_tendsto_flow (Q : ι → ι → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (z : State ι) :
    Filter.Tendsto (fun n : ℕ => restore ((step Q (T / n))^[n] z))
      Filter.atTop (𝓝 (restore (flow Q T z))) :=
  (restore_lipschitz.continuous.tendsto _).comp (iterate_tendsto_flow Q T hT z)

end

end KerrKoopman.FiniteFlow
