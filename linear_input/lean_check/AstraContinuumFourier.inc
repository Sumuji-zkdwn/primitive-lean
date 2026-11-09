
/-!
# The actual interval Fourier projection in the continuum relative-energy rate

The projection is now the actual coefficient operator. Its self-adjointness,
idempotence, derivative commutation, and residual annihilation are proved,
not hypotheses. The supplied classical comparison field must have the stated
finite magnetic polynomial and actual projection residual. Construction of
those fields from the existing L2 Galerkin ODE remains a separate bridge.
-/

namespace KerrKoopman.ContinuumFourier

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Interval
open ContinuumRelative IntervalFourier FourierSupBounds

theorem deriv_normalizedEnergy_le_fourier {s : Set ℝ}
    (u : ClassicalKerrPair 0 period s) (N : ℕ)
    (t M A B : ℝ) (hs : s ∈ 𝓝 t) (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (bound : ℝ → ℝ) (hb : IntervalIntegrable bound volume 0 period)
    (hbound : ∀ x ∈ uIcc 0 period, ∀ z ∈ s, |u.rate z x| ≤ bound x)
    (c : ℝ) (ac bc : Fin N → ℝ)
    (hJ : u.J t = polynomial c (fun k : Fin N => ((k.val+1 : ℕ) : ℝ)) ac bc)
    (hr : ∀ x, u.residual t x = u.Vx t x-deriv (projection N (u.V t)) x)
    (hHx : ∀ x ∈ Icc 0 period, |u.Hx t x| ≤ M)
    (hA2 : (∫ x in 0..period, (u.Hx t x-projection N (u.Hx t) x)^2)/period ≤ A^2)
    (hB2 : (∫ x in 0..period, (u.E t x-projection N (u.E t) x)^2)/period ≤ B^2) :
    deriv (ContinuumGalerkin.ClassicalKerrPair.normalizedEnergy u) t ≤
      (3*M+1)*ContinuumGalerkin.ClassicalKerrPair.normalizedEnergy u t + A^2/2 + A*B := by
  have ht : t ∈ s := mem_of_mem_nhds hs
  have hp : 0 < period := by unfold period; positivity
  have hPJ : projection N (u.J t) = u.J t := by
    rw [hJ, projection_polynomial]
  have her : u.residual t = fun x => u.Vx t x-deriv (projection N (u.V t)) x := by
    funext x
    exact hr x
  have hPr : projection N (u.residual t) = fun _ => 0 := by
    rw [her]
    exact projection_residual_zero N (u.V t) (u.Vx t)
      (u.spatial_V t ht) (u.continuous_Vx t) (u.periodic_V t ht)
  have hPV (x : ℝ) : HasDerivAt (projection N (u.V t))
      (deriv (projection N (u.V t)) x) x :=
    (projection_hasDerivAt N (u.V t) x).differentiableAt.hasDerivAt
  exact ContinuumGalerkin.ClassicalKerrPair.deriv_normalizedEnergy_le_projection u t M A B
    hs hp hM hA hB bound hb hbound (actualProjection N) (deriv (projection N (u.V t)))
    hPJ hPr hPV (projection_deriv_continuous N (u.V t)) (projection_endpoint N (u.V t))
    hr hHx (by simpa only [sub_zero, actualProjection] using hA2)
    (by simpa only [sub_zero, actualProjection] using hB2)

end
end KerrKoopman.ContinuumFourier
