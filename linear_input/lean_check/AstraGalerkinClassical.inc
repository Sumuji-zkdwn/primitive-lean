
/-!
# Actual classical fields decoded from the actual real L2 Galerkin ODE

Spatial derivatives are derivatives of smooth real functions, time derivatives
come from the existing global finite flow, and the projected material is the
actual interval Fourier projection. No PDE evolution identity is assumed.
-/

namespace KerrKoopman.GalerkinClassical

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open MaterialL2 ExplicitMaterial FiniteRepresentatives RealFourierDerivative

abbrev Circle := FiniteRepresentatives.Circle

def continuousMaterial (f : C(Circle, ℝ)) : C(Circle, ℝ) :=
  ⟨fun x => electricOfDisplacement (f x), electricOfDisplacement_lipschitz.continuous.comp f.continuous⟩

theorem toL2_continuousMaterial (f : C(Circle, ℝ)) :
    toL2 (continuousMaterial f) = material (toL2 f) := by
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) AddCircle.haarAddCircle
    (continuousMaterial f), material_ae (toL2 f),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) AddCircle.haarAddCircle f] with x hx hy hz
  change (toL2 (continuousMaterial f)) x = continuousMaterial f x at hx
  change (toL2 f) x = f x at hz
  rw [hx, hy, Function.comp_apply, hz]
  rfl

theorem representative_projectedMaterial (N : ℕ) (d : RealGalerkin.space N) :
    representative N (RealGalerkin.projectedMaterial N d) =
      circleProjection N (continuousMaterial (representative N d)) := by
  apply representative_unique
  rw [toL2_circleProjection, toL2_continuousMaterial, toL2_representative,
    RealGalerkin.projectedMaterial_coe]

/-- The actual projected L2 material decodes to the actual interval coefficient operator. -/
theorem lift_projectedMaterial (N : ℕ) (d : RealGalerkin.space N) :
    lift N (RealGalerkin.projectedMaterial N d) =
      IntervalFourier.projection N (fun x => electricOfDisplacement (lift N d x)) := by
  change realLift (representative N (RealGalerkin.projectedMaterial N d)) = _
  rw [representative_projectedMaterial, realLift_circleProjection]
  rfl

def displacement (N : ℕ) (z : GalerkinFlow.State N) (t : ℝ) : ℝ → ℝ :=
  lift N (GalerkinFlow.flow N t z).fst

def magnetic (N : ℕ) (z : GalerkinFlow.State N) (t : ℝ) : ℝ → ℝ :=
  lift N (GalerkinFlow.flow N t z).snd

def electric (N : ℕ) (z : GalerkinFlow.State N) (t x : ℝ) : ℝ :=
  electricOfDisplacement (displacement N z t x)

theorem displacement_space (N : ℕ) (z : GalerkinFlow.State N) (t x : ℝ) :
    HasDerivAt (displacement N z t)
      (lift N (finiteDerivative N (GalerkinFlow.flow N t z).fst) x) x :=
  lift_hasDerivAt N _ x

theorem magnetic_space (N : ℕ) (z : GalerkinFlow.State N) (t x : ℝ) :
    HasDerivAt (magnetic N z t)
      (lift N (finiteDerivative N (GalerkinFlow.flow N t z).snd) x) x :=
  lift_hasDerivAt N _ x

theorem displacement_contDiff (N : ℕ) (z : GalerkinFlow.State N) (t : ℝ) :
    ContDiff ℝ ⊤ (displacement N z t) := lift_contDiff N _

theorem magnetic_contDiff (N : ℕ) (z : GalerkinFlow.State N) (t : ℝ) :
    ContDiff ℝ ⊤ (magnetic N z t) := lift_contDiff N _

theorem electric_contDiff (N : ℕ) (z : GalerkinFlow.State N) (t : ℝ) :
    ContDiff ℝ ⊤ (electric N z t) :=
  contDiff_electricOfDisplacement.comp (displacement_contDiff N z t)

theorem displacement_time (N : ℕ) (z : GalerkinFlow.State N) (t x : ℝ) :
    HasDerivAt (fun s => displacement N z s x) (-deriv (magnetic N z t) x) t := by
  let ev : GalerkinFlow.State N →L[ℝ] ℝ :=
    (evaluate N x).comp (WithLp.fstL 2 ℝ (RealGalerkin.space N) (RealGalerkin.space N))
  have hd := ev.hasFDerivAt.comp_hasDerivAt t (GalerkinFlow.hasDerivAt_flow N t z)
  change HasDerivAt (fun s => displacement N z s x)
    (lift N (-finiteDerivative N (GalerkinFlow.flow N t z).snd) x) t at hd
  rw [(magnetic_space N z t x).deriv]
  simpa only [lift, map_neg, ContinuousMap.neg_apply] using hd

theorem magnetic_time (N : ℕ) (z : GalerkinFlow.State N) (t x : ℝ) :
    HasDerivAt (fun s => magnetic N z s x)
      (-deriv (IntervalFourier.projection N (electric N z t)) x) t := by
  let ev : GalerkinFlow.State N →L[ℝ] ℝ :=
    (evaluate N x).comp (WithLp.sndL 2 ℝ (RealGalerkin.space N) (RealGalerkin.space N))
  have hd := ev.hasFDerivAt.comp_hasDerivAt t (GalerkinFlow.hasDerivAt_flow N t z)
  change HasDerivAt (fun s => magnetic N z s x)
    (lift N (-finiteDerivative N (RealGalerkin.projectedMaterial N
      (GalerkinFlow.flow N t z).fst)) x) t at hd
  have he : IntervalFourier.projection N (electric N z t) =
      lift N (RealGalerkin.projectedMaterial N (GalerkinFlow.flow N t z).fst) :=
    (lift_projectedMaterial N _).symm
  rw [he, lift_deriv]
  simpa only [lift, map_neg, ContinuousMap.neg_apply] using hd

theorem electric_time (N : ℕ) (z : GalerkinFlow.State N) (t x : ℝ) :
    HasDerivAt (fun s => electric N z s x)
      (-deriv (magnetic N z t) x/(1+(electric N z t x)^2)) t := by
  have hd := (hasDerivAt_electricOfDisplacement (displacement N z t x)).comp t
    (displacement_time N z t x)
  convert hd using 1
  dsimp [electric]
  ring

theorem magnetic_endpoint (N : ℕ) (z : GalerkinFlow.State N) (t : ℝ) :
    magnetic N z t (2*Real.pi) = magnetic N z t 0 := lift_endpoint N _

theorem electric_endpoint (N : ℕ) (z : GalerkinFlow.State N) (t : ℝ) :
    electric N z t (2*Real.pi) = electric N z t 0 := by
  unfold electric displacement
  rw [lift_endpoint]

end
end KerrKoopman.GalerkinClassical
