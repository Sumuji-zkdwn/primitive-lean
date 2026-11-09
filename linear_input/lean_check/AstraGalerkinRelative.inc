
/-!
# Relative energy against the actual global Fourier-Galerkin flow

The comparison fields and their projection residual are constructed from the
actual finite ODE. The supplied continuum base remains a classical solution;
no continuum existence theorem or tail budget is assumed proved by this file.
-/

namespace KerrKoopman.GalerkinClassical

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter
open scoped Topology Interval
open FiniteRepresentatives ContinuumRelative

theorem projection_lift (N : ℕ) (f : RealGalerkin.space N) :
    IntervalFourier.projection N (lift N f) = lift N f := by
  have hc : circleProjection N (representative N f) = representative N f := by
    apply toL2_injective
    rw [toL2_circleProjection, toL2_representative,
      RealGalerkin.projection_eq_self N f.property]
  have hl := congrArg realLift hc
  rw [realLift_circleProjection] at hl
  exact hl

/-- Replace the comparison fields by the explicitly constructed finite Galerkin trajectory. -/
def withGalerkin {s : Set ℝ} (base : ClassicalKerrPair 0 IntervalFourier.period s)
    (N : ℕ) (z : GalerkinFlow.State N) : ClassicalKerrPair 0 IntervalFourier.period s where
  E := base.E
  H := base.H
  V := electric N z
  J := magnetic N z
  Ex := base.Ex
  Hx := base.Hx
  Vx := fun t => deriv (electric N z t)
  Jx := fun t => deriv (magnetic N z t)
  residual := fun t x => deriv (electric N z t) x -
    deriv (IntervalFourier.projection N (electric N z t)) x
  continuous_E := base.continuous_E
  continuous_H := base.continuous_H
  continuous_V := fun t => (electric_contDiff N z t).continuous
  continuous_J := fun t => (magnetic_contDiff N z t).continuous
  continuous_Ex := base.continuous_Ex
  continuous_Hx := base.continuous_Hx
  continuous_Vx := fun t => (electric_contDiff N z t).continuous_deriv (by simp)
  continuous_Jx := fun t => (magnetic_contDiff N z t).continuous_deriv (by simp)
  continuous_residual := fun t =>
    ((electric_contDiff N z t).continuous_deriv (by simp)).sub
      (IntervalFourier.projection_deriv_continuous N (electric N z t))
  spatial_E := base.spatial_E
  spatial_H := base.spatial_H
  spatial_V := fun t _ x => ((electric_contDiff N z t).differentiable (by simp) x).hasDerivAt
  spatial_J := fun t _ x => ((magnetic_contDiff N z t).differentiable (by simp) x).hasDerivAt
  time_E := base.time_E
  time_H := base.time_H
  time_V := fun t _ x => electric_time N z t x
  time_J := fun t _ x => by
    convert magnetic_time N z t x using 1
    ring
  periodic_E := base.periodic_E
  periodic_H := base.periodic_H
  periodic_V := fun t _ => electric_endpoint N z t
  periodic_J := fun t _ => magnetic_endpoint N z t

/-- Actual continuum-versus-Galerkin rate: no abstract projection or comparison evolution law remains. -/
theorem actual_galerkin_relative_rate {s : Set ℝ}
    (base : ClassicalKerrPair 0 IntervalFourier.period s)
    (N : ℕ) (z : GalerkinFlow.State N) (t M A B : ℝ)
    (hs : s ∈ 𝓝 t) (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (bound : ℝ → ℝ) (hb : IntervalIntegrable bound volume 0 IntervalFourier.period)
    (hbound : ∀ x ∈ uIcc 0 IntervalFourier.period, ∀ q ∈ s,
      |(withGalerkin base N z).rate q x| ≤ bound x)
    (hHx : ∀ x ∈ Icc 0 IntervalFourier.period, |base.Hx t x| ≤ M)
    (hA2 : (∫ x in 0..IntervalFourier.period,
      (base.Hx t x-IntervalFourier.projection N (base.Hx t) x)^2)/IntervalFourier.period ≤ A^2)
    (hB2 : (∫ x in 0..IntervalFourier.period,
      (base.E t x-IntervalFourier.projection N (base.E t) x)^2)/IntervalFourier.period ≤ B^2) :
    deriv (ContinuumGalerkin.ClassicalKerrPair.normalizedEnergy (withGalerkin base N z)) t ≤
      (3*M+1)*ContinuumGalerkin.ClassicalKerrPair.normalizedEnergy (withGalerkin base N z) t +
        A^2/2 + A*B := by
  have hJ : (withGalerkin base N z).J t =
      FourierSupBounds.polynomial (IntervalFourier.mean (magnetic N z t))
        (fun k : Fin N => ((k.val+1 : ℕ) : ℝ))
        (fun k => IntervalFourier.cosCoeff (magnetic N z t) (k.val+1))
        (fun k => IntervalFourier.sinCoeff (magnetic N z t) (k.val+1)) :=
    (projection_lift N (GalerkinFlow.flow N t z).snd).symm
  exact ContinuumFourier.deriv_normalizedEnergy_le_fourier (withGalerkin base N z) N t M A B
    hs hM hA hB bound hb hbound (IntervalFourier.mean (magnetic N z t))
    (fun k => IntervalFourier.cosCoeff (magnetic N z t) (k.val+1))
    (fun k => IntervalFourier.sinCoeff (magnetic N z t) (k.val+1))
    hJ (fun _ => rfl) hHx hA2 hB2

end
end KerrKoopman.GalerkinClassical
