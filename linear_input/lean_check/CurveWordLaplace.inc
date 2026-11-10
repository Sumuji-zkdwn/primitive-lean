/-!
Uniqueness of real Laplace transforms of finite Borel measures, with explicit
exponential integrability. The proof uses analytic continuation of the complex
moment-generating function and the uniqueness of characteristic functions.
Finite Boltzmann endpoint measures connect this theorem to the word partition
function; equal endpoint measures do not identify labels within a fiber.
-/

noncomputable section

namespace LinearInputCurveWordLaplace
open MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

/-- Equality at zero records the total mass, including the zero measure. -/
theorem zero_iff_of_mgf_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {X : Ω → ℝ} {Y : Ω' → ℝ} (h : mgf X μ = mgf Y ν) : μ = 0 ↔ ν = 0 := by
  have hm : μ.real Set.univ = ν.real Set.univ := by
    simpa only [mgf_zero'] using congrFun h 0
  rw [← Measure.measure_univ_eq_zero, ← Measure.measure_univ_eq_zero,
    ← measureReal_eq_zero_iff, ← measureReal_eq_zero_iff, hm]

/-- A real moment-generating function finite on a neighborhood of zero
determines the pushforward distribution of a measurable real observable. -/
theorem map_eq_of_mgf_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {X : Ω → ℝ} {Y : Ω' → ℝ}
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y ν)
    (hnear : (0 : ℝ) ∈ interior (integrableExpSet X μ))
    (h : mgf X μ = mgf Y ν) : μ.map X = ν.map Y := by
  apply Measure.ext_of_charFun
  funext t
  rw [← complexMGF_mul_I hX, ← complexMGF_mul_I hY]
  apply eqOn_complexMGF_of_mgf' h (zero_iff_of_mgf_eq h)
  simpa using hnear

section Banach
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E]

/-- The real Laplace transform indexed by continuous linear functionals. -/
def laplace (μ : Measure E) (L : E →L[ℝ] ℝ) : ℝ := ∫ x, Real.exp (L x) ∂μ

theorem laplace_smul (μ : Measure E) (L : E →L[ℝ] ℝ) (t : ℝ) :
    laplace μ (t • L) = mgf L μ t := by
  simp [laplace, mgf]

variable [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

/-- Laplace uniqueness in a separable real Banach space. Integrability near
zero is required in every dual direction; totalized nonintegrable integrals
alone do not suffice. -/
theorem measure_eq_of_laplace_eq {μ ν : Measure E}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hnear : ∀ L : E →L[ℝ] ℝ, (0 : ℝ) ∈ interior (integrableExpSet L μ))
    (h : ∀ L : E →L[ℝ] ℝ, laplace μ L = laplace ν L) : μ = ν := by
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one]
  have hm : mgf L μ = mgf L ν := by
    funext t
    simpa only [laplace_smul] using h (t • L)
  rw [map_eq_of_mgf_eq L.measurable.aemeasurable L.measurable.aemeasurable (hnear L) hm]

/-- An everywhere finite Laplace transform is a sufficient explicit condition. -/
theorem measure_eq_of_laplace_eq_of_integrable {μ ν : Measure E}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hint : ∀ L : E →L[ℝ] ℝ, Integrable (fun x => Real.exp (L x)) μ)
    (h : ∀ L : E →L[ℝ] ℝ, laplace μ L = laplace ν L) : μ = ν := by
  apply measure_eq_of_laplace_eq (h := h)
  intro L
  have he : integrableExpSet L μ = Set.univ := by
    ext t
    simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    simpa using hint (t • L)
  simp [he]

end Banach

section FiniteEndpoints
variable {ι E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]

/-- A finite endpoint measure retains the sum of Boltzmann weights at a point. -/
def endpointMeasure (S : Finset ι) (z : ι → E) (F : ι → ℝ) (β : ℝ) : Measure E :=
  ∑ w ∈ S, ENNReal.ofReal (Real.exp (-β * F w)) • Measure.dirac (z w)

instance endpointMeasure_finite (S : Finset ι) (z : ι → E) (F : ι → ℝ) (β : ℝ) :
    IsFiniteMeasure (endpointMeasure S z F β) := by
  constructor
  unfold endpointMeasure
  simp only [Measure.finset_sum_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
    (Set.mem_univ _), smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.ofReal_lt_top)

theorem endpointMeasure_integrable (S : Finset ι) (z : ι → E) (F : ι → ℝ)
    (β : ℝ) (f : E → ℝ) : Integrable f (endpointMeasure S z F β) := by
  apply integrable_finset_sum_measure.mpr
  intro w _
  exact (integrable_dirac (by finiteness)).smul_measure (by finiteness)

theorem integral_endpointMeasure (S : Finset ι) (z : ι → E) (F : ι → ℝ)
    (β : ℝ) (f : E → ℝ) :
    (∫ x, f x ∂endpointMeasure S z F β) =
      ∑ w ∈ S, Real.exp (-β * F w) * f (z w) := by
  unfold endpointMeasure
  rw [integral_finset_sum_measure]
  · apply Finset.sum_congr rfl
    intro w _
    rw [integral_smul_measure, integral_dirac]
    simp [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  · intro w _
    exact (integrable_dirac (by finiteness)).smul_measure (by finiteness)

end FiniteEndpoints

section EndpointUniqueness
variable {ι κ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

theorem laplace_endpointMeasure (S : Finset ι) (z : ι → E) (F : ι → ℝ)
    (β : ℝ) (L : E →L[ℝ] ℝ) :
    laplace (endpointMeasure S z F β) L =
      ∑ w ∈ S, Real.exp (-β * F w + L (z w)) := by
  rw [laplace, integral_endpointMeasure]
  apply Finset.sum_congr rfl
  intro w _
  rw [Real.exp_add]

/-- The word partition function is exactly the Laplace transform at βL. -/
theorem partition_eq_laplace_endpointMeasure (S : Finset ι) (z : ι → E)
    (F : ι → ℝ) (β : ℝ) (L : E →L[ℝ] ℝ) :
    LinearInputCurveWordThermodynamics.partition S (fun w => F w - L (z w)) β =
      laplace (endpointMeasure S z F β) (β • L) := by
  rw [laplace_endpointMeasure]
  unfold LinearInputCurveWordThermodynamics.partition
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Equality of all real exponential sums determines the finite endpoint
measure, even when different words share an endpoint or have different costs. -/
theorem endpointMeasure_eq_of_exponential_sums_eq
    (S : Finset ι) (T : Finset κ) (z : ι → E) (z' : κ → E)
    (F : ι → ℝ) (F' : κ → ℝ) (β : ℝ)
    (h : ∀ L : E →L[ℝ] ℝ,
      (∑ w ∈ S, Real.exp (-β * F w + L (z w))) =
        ∑ w ∈ T, Real.exp (-β * F' w + L (z' w))) :
    endpointMeasure S z F β = endpointMeasure T z' F' β := by
  apply measure_eq_of_laplace_eq_of_integrable
  · intro L
    exact endpointMeasure_integrable S z F β _
  · intro L
    simpa only [laplace_endpointMeasure] using h L

/-- At any nonzero fixed inverse temperature, all linear-input partition
values determine the endpoint Boltzmann measure. The finite family and costs
need not be the same on the two sides. -/
theorem endpointMeasure_eq_of_partition_eq
    (S : Finset ι) (T : Finset κ) (z : ι → E) (z' : κ → E)
    (F : ι → ℝ) (F' : κ → ℝ) (β : ℝ) (hβ : β ≠ 0)
    (h : ∀ L : E →L[ℝ] ℝ,
      LinearInputCurveWordThermodynamics.partition S (fun w => F w - L (z w)) β =
      LinearInputCurveWordThermodynamics.partition T (fun w => F' w - L (z' w)) β) :
    endpointMeasure S z F β = endpointMeasure T z' F' β := by
  apply measure_eq_of_laplace_eq_of_integrable
  · intro L
    exact endpointMeasure_integrable S z F β _
  · intro L
    have hh := h (β⁻¹ • L)
    simpa only [partition_eq_laplace_endpointMeasure, smul_smul,
      mul_inv_cancel₀ hβ, one_smul] using hh

end EndpointUniqueness

end LinearInputCurveWordLaplace
