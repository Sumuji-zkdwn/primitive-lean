
/-!
# Actual real Fourier-Galerkin Kerr flow and restored error bound

Both the spatial derivative and the projected nonlinear material map are
constructed on the actual real trigonometric subspace. No arbitrary Q or G
remains in the final theorem. The decoder restores (E,H)=(g(D),H) as real L2
classes and is nonexpansive, so the explicit iteration error bound survives
restoration. The cutoff N is fixed in the convergence theorem; this does not
yet assert convergence to a continuum PDE solution as N tends to infinity.
-/

namespace KerrKoopman.GalerkinFlow

noncomputable section

open MaterialL2
open scoped Topology

abbrev State (N : ℕ) := HilbertShear.State (RealGalerkin.space N)

abbrev Fields := HilbertShear.State RealCircleL2

/-- Initial-only exact orthogonal projection of displacement and magnetic field. -/
def encode (N : ℕ) (z : Fields) : State N :=
  WithLp.toLp 2 ((RealGalerkin.space N).orthogonalProjectionOnto z.fst,
    (RealGalerkin.space N).orthogonalProjectionOnto z.snd)

/-- Restoration of physical electric and magnetic fields. -/
def decode (N : ℕ) (z : State N) : Fields :=
  WithLp.toLp 2 (material (z.fst : RealCircleL2), (z.snd : RealCircleL2))

/-- One explicit spatial Galerkin step, with exactly two algebraic shears. -/
def step (N : ℕ) (h : ℝ) : State N → State N :=
  HilbertShear.lieStep (RealFourierDerivative.finiteDerivative N)
    (RealGalerkin.projectedMaterial N) h

/-- Actual physical-time Galerkin vector field on the constructed real space. -/
def vectorField (N : ℕ) : State N → State N :=
  HilbertShear.field (RealFourierDerivative.finiteDerivative N)
    (RealGalerkin.projectedMaterial N)

/-- Unique global solution of the actual real Fourier-Galerkin system. -/
def flow (N : ℕ) (t : ℝ) : State N → State N :=
  HilbertFlow.flow (RealFourierDerivative.finiteDerivative N)
    (RealGalerkin.projectedMaterial N) (RealGalerkin.projectedMaterial_lipschitz N) t

theorem step_fst (N : ℕ) (h : ℝ) (z : State N) :
    (step N h z).fst = z.fst - h • RealFourierDerivative.finiteDerivative N z.snd := rfl

theorem step_snd (N : ℕ) (h : ℝ) (z : State N) :
    (step N h z).snd = z.snd - h • RealFourierDerivative.finiteDerivative N
      (RealGalerkin.projectedMaterial N
        (z.fst - h • RealFourierDerivative.finiteDerivative N z.snd)) := rfl

theorem encode_norm_le (N : ℕ) (z : Fields) : ‖encode N z‖ ≤ ‖z‖ := by
  have hf : ‖(encode N z).fst‖ ≤ ‖z.fst‖ :=
    (RealGalerkin.space N).norm_orthogonalProjectionOnto_apply_le z.fst
  have hs : ‖(encode N z).snd‖ ≤ ‖z.snd‖ :=
    (RealGalerkin.space N).norm_orthogonalProjectionOnto_apply_le z.snd
  have hf2 : ‖(encode N z).fst‖ ^ 2 ≤ ‖z.fst‖ ^ 2 := by gcongr
  have hs2 : ‖(encode N z).snd‖ ^ 2 ≤ ‖z.snd‖ ^ 2 := by gcongr
  have hsq : ‖encode N z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
    linarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

theorem decode_constitutive_ae (N : ℕ) (z : State N) :
    ∀ᵐ x ∂AddCircle.haarAddCircle,
      (decode N z).fst x + (decode N z).fst x ^ 3 / 3 = (z.fst : RealCircleL2) x :=
  material_constitutive_ae (z.fst : RealCircleL2)

theorem hasDerivAt_flow (N : ℕ) (t : ℝ) (z : State N) :
    HasDerivAt (fun s => flow N s z) (vectorField N (flow N t z)) t :=
  HilbertFlow.hasDerivAt_flow _ _ _ _ _

theorem flow_zero (N : ℕ) (z : State N) : flow N 0 z = z :=
  HilbertFlow.flow_zero _ _ _ _

theorem flow_add (N : ℕ) (t s : ℝ) (z : State N) :
    flow N (t + s) z = flow N t (flow N s z) := HilbertFlow.flow_add _ _ _ _ _ _

theorem flow_norm_sub_le (N : ℕ) (t : ℝ) (ht : 0 ≤ t) (z w : State N) :
    ‖flow N t z - flow N t w‖ ≤ Real.exp ((N : ℝ) * t) * ‖z - w‖ := by
  have hb := HilbertFlow.flow_norm_sub_le (RealFourierDerivative.finiteDerivative N)
    (RealGalerkin.projectedMaterial N) (RealGalerkin.projectedMaterial_lipschitz N) t ht z w
  exact hb.trans (by
    gcongr
    exact RealFourierDerivative.finiteDerivative_operator_norm_le N)

theorem flow_norm_le (N : ℕ) (t : ℝ) (ht : 0 ≤ t) (z : State N) :
    ‖flow N t z‖ ≤ Real.exp ((N : ℝ) * t) * ‖z‖ := by
  have hb := HilbertFlow.flow_norm_le (RealFourierDerivative.finiteDerivative N)
    (RealGalerkin.projectedMaterial N) (RealGalerkin.projectedMaterial_lipschitz N)
    (RealGalerkin.projectedMaterial_zero N) t ht z
  exact hb.trans (by
    gcongr
    exact RealFourierDerivative.finiteDerivative_operator_norm_le N)

theorem decode_norm_sub_le (N : ℕ) (z w : State N) :
    ‖decode N z - decode N w‖ ≤ ‖z - w‖ := by
  have hf : ‖(decode N z - decode N w).fst‖ ≤ ‖(z - w).fst‖ :=
    material_norm_sub_le (z.fst : RealCircleL2) (w.fst : RealCircleL2)
  have hs : ‖(decode N z - decode N w).snd‖ = ‖(z - w).snd‖ := rfl
  have hf2 : ‖(decode N z - decode N w).fst‖ ^ 2 ≤ ‖(z - w).fst‖ ^ 2 := by gcongr
  have hsq : ‖decode N z - decode N w‖ ^ 2 ≤ ‖z - w‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2, hs]
    linarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

theorem decode_lipschitz (N : ℕ) : LipschitzWith 1 (decode N) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using decode_norm_sub_le N z w

theorem step_flow_error_le (N : ℕ) (h : ℝ) (hh : 0 ≤ h) (z : State N) :
    ‖step N h z - flow N h z‖ ≤
      (3 / 2 : ℝ) * N * h ^ 2 * Real.exp ((N : ℝ) * h) * ‖vectorField N z‖ := by
  have hb := HilbertError.lieStep_flow_error_le (RealFourierDerivative.finiteDerivative N)
    (RealGalerkin.projectedMaterial N) (RealGalerkin.projectedMaterial_lipschitz N) h hh z
  exact hb.trans (by
    dsimp only [vectorField]
    gcongr <;> exact RealFourierDerivative.finiteDerivative_operator_norm_le N)

/-- Fully instantiated initial-only finite-time certificate for exact arithmetic. -/
theorem finite_time_error_le (N : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (z : State N) (n : ℕ) (hn : 0 < n) :
    ‖(step N (T / n))^[n] z - flow N T z‖ ≤
      ((3 / 2 : ℝ) * (N : ℝ) ^ 2 * T ^ 2 * ‖z‖ / n) * Real.exp ((N : ℝ) * T) := by
  have hb := HilbertIteration.finite_time_error_le (RealFourierDerivative.finiteDerivative N)
    (RealGalerkin.projectedMaterial N) (RealGalerkin.projectedMaterial_lipschitz N)
    (RealGalerkin.projectedMaterial_zero N) T hT z n hn
  exact hb.trans (by
    gcongr <;> exact RealFourierDerivative.finiteDerivative_operator_norm_le N)

theorem restored_error_le (N : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (z : State N) (n : ℕ) (hn : 0 < n) :
    ‖decode N ((step N (T / n))^[n] z) - decode N (flow N T z)‖ ≤
      ((3 / 2 : ℝ) * (N : ℝ) ^ 2 * T ^ 2 * ‖z‖ / n) * Real.exp ((N : ℝ) * T) :=
  (decode_norm_sub_le N _ _).trans (finite_time_error_le N T hT z n hn)

/-- Exact-arithmetic restored error controlled by the original input alone.
This compares with the Galerkin flow from that projected input, not with an
unconstructed continuum PDE solution. -/
theorem initial_only_restored_error_le (N : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (z₀ : Fields) (n : ℕ) (hn : 0 < n) :
    ‖decode N ((step N (T / n))^[n] (encode N z₀)) -
        decode N (flow N T (encode N z₀))‖ ≤
      ((3 / 2 : ℝ) * (N : ℝ) ^ 2 * T ^ 2 * ‖z₀‖ / n) * Real.exp ((N : ℝ) * T) := by
  apply (restored_error_le N T hT (encode N z₀) n hn).trans
  gcongr
  exact encode_norm_le N z₀

theorem iterate_tendsto_flow (N : ℕ) (T : ℝ) (hT : 0 ≤ T) (z : State N) :
    Filter.Tendsto (fun n : ℕ => (step N (T / n))^[n] z)
      Filter.atTop (𝓝 (flow N T z)) :=
  HilbertIteration.iterate_tendsto_flow (RealFourierDerivative.finiteDerivative N)
    (RealGalerkin.projectedMaterial N) (RealGalerkin.projectedMaterial_lipschitz N)
    (RealGalerkin.projectedMaterial_zero N) T hT z

/-- The repeated algebraic formula converges after restoring the actual fields. -/
theorem restored_tendsto_flow (N : ℕ) (T : ℝ) (hT : 0 ≤ T) (z : State N) :
    Filter.Tendsto (fun n : ℕ => decode N ((step N (T / n))^[n] z))
      Filter.atTop (𝓝 (decode N (flow N T z))) :=
  (decode_lipschitz N).continuous.continuousAt.tendsto.comp
    (iterate_tendsto_flow N T hT z)

/-- A possibly sharper certificate from fields evaluated at computed states. -/
theorem evaluated_error_le (N : ℕ) (h : ℝ) (hh : 0 ≤ h) (z : State N) (n : ℕ) :
    ‖(step N h)^[n] z - flow N ((n : ℝ) * h) z‖ ≤
      ((3 / 2 : ℝ) * N * h ^ 2) * Real.exp ((n : ℝ) * N * h) *
        ∑ k ∈ Finset.range n, ‖vectorField N ((step N h)^[k] z)‖ := by
  have hb := HilbertIteration.evaluated_iterate_error_le (RealFourierDerivative.finiteDerivative N)
    (RealGalerkin.projectedMaterial N) (RealGalerkin.projectedMaterial_lipschitz N) h hh z n
  exact hb.trans (by
    dsimp only [step, vectorField]
    gcongr <;> exact RealFourierDerivative.finiteDerivative_operator_norm_le N)

end

end KerrKoopman.GalerkinFlow
