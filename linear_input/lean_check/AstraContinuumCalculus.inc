
/-!
# Real periodic integration and differentiation

The spatial domain is an actual real interval with Lebesgue integration.
Endpoint equality is sufficient for the periodic cancellation. Derivatives,
continuity, and domination are explicit; no finite-dimensional replacement
of the spatial integral is used.
-/

namespace KerrKoopman.ContinuumCalculus

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Interval

/-- The integral of an actual product derivative vanishes when both factors
agree at the interval endpoints. -/
theorem periodic_product_integral (u v du dv : ℝ → ℝ) (a b : ℝ)
    (hu : ∀ x, HasDerivAt u (du x) x) (hv : ∀ x, HasDerivAt v (dv x) x)
    (hdu : Continuous du) (hdv : Continuous dv)
    (huab : u b = u a) (hvab : v b = v a) :
    (∫ x in a..b, du x * v x + u x * dv x) = 0 := by
  rw [intervalIntegral.integral_deriv_mul_eq_sub
    (fun x _ => hu x) (fun x _ => hv x) (hdu.intervalIntegrable a b)
    (hdv.intervalIntegrable a b)]
  rw [huab, hvab, sub_self]

/-- Skewness of the spatial derivative follows from periodic integration by
parts, not from an assumed skew matrix or pairing identity. -/
theorem periodic_skew_integral (u v du dv : ℝ → ℝ) (a b : ℝ)
    (hu : ∀ x, HasDerivAt u (du x) x) (hv : ∀ x, HasDerivAt v (dv x) x)
    (hdu : Continuous du) (hdv : Continuous dv)
    (huab : u b = u a) (hvab : v b = v a) :
    (∫ x in a..b, u x * dv x) = -(∫ x in a..b, du x * v x) := by
  have cu : Continuous u := continuous_iff_continuousAt.mpr (fun x => (hu x).continuousAt)
  have cv : Continuous v := continuous_iff_continuousAt.mpr (fun x => (hv x).continuousAt)
  have hp := periodic_product_integral u v du dv a b hu hv hdu hdv huab hvab
  have hadd : (∫ x in a..b, du x * v x + u x * dv x) =
      (∫ x in a..b, du x * v x) + (∫ x in a..b, u x * dv x) :=
    intervalIntegral.integral_add ((hdu.mul cv).intervalIntegrable a b)
      ((cu.mul hdv).intervalIntegrable a b)
  rw [hadd] at hp
  linarith

/-- A convenient actual interval-integral differentiation theorem with
continuous spatial slices and a local integrable bound on the time rate. -/
theorem integral_hasDerivAt_of_continuous_slices
    (F G : ℝ → ℝ → ℝ) (a b t : ℝ) (s : Set ℝ) (bound : ℝ → ℝ)
    (hs : s ∈ 𝓝 t) (hF : ∀ z, Continuous (F z)) (hG : Continuous (G t))
    (hb : IntervalIntegrable bound volume a b)
    (hbound : ∀ x ∈ Set.uIcc a b, ∀ z ∈ s, |G z x| ≤ bound x)
    (hd : ∀ x ∈ Set.uIcc a b, ∀ z ∈ s, HasDerivAt (fun w => F w x) (G z x) z) :
    HasDerivAt (fun z => ∫ x in a..b, F z x) (∫ x in a..b, G t x) t := by
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs (Filter.Eventually.of_forall (fun z => (hF z).aestronglyMeasurable))
    ((hF t).intervalIntegrable a b) hG.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x hx z hz => ?_)) hb
    (Filter.Eventually.of_forall (fun x hx z hz => ?_))).2
  · simpa only [Real.norm_eq_abs] using hbound x (Set.uIoc_subset_uIcc hx) z hz
  · exact hd x (Set.uIoc_subset_uIcc hx) z hz

/-- A projection residual is transferred to the base spatial derivative by
actual periodic IBP and integral self-adjointness. The operator laws and range
membership are explicit; this does not construct a Fourier projection. -/
theorem projection_residual_pairing
    (P : (ℝ → ℝ) → (ℝ → ℝ)) (H J V Hx Vx PVx r : ℝ → ℝ) (a b : ℝ)
    (hPcont : ∀ f, Continuous f → Continuous (P f))
    (hself : ∀ f g, Continuous f → Continuous g →
      (∫ x in a..b, P f x * g x) = ∫ x in a..b, f x * P g x)
    (hPJ : P J = J) (hPr : P r = fun _ => 0)
    (cJ : Continuous J) (cr : Continuous r)
    (hH : ∀ x, HasDerivAt H (Hx x) x) (hV : ∀ x, HasDerivAt V (Vx x) x)
    (hPV : ∀ x, HasDerivAt (P V) (PVx x) x)
    (cHx : Continuous Hx) (cVx : Continuous Vx) (cPVx : Continuous PVx)
    (pH : H b = H a) (pV : V b = V a) (pPV : P V b = P V a)
    (hr : ∀ x, r x = Vx x - PVx x) :
    (∫ x in a..b, (J x - H x) * r x) =
      ∫ x in a..b, (Hx x - P Hx x) * V x := by
  have cH : Continuous H := continuous_iff_continuousAt.mpr (fun x => (hH x).continuousAt)
  have cV : Continuous V := continuous_iff_continuousAt.mpr (fun x => (hV x).continuousAt)
  have cPV := hPcont V cV
  have cPHx := hPcont Hx cHx
  have ho : (∫ x in a..b, J x * r x) = 0 := by
    calc
      _ = ∫ x in a..b, P J x * r x := by rw [hPJ]
      _ = ∫ x in a..b, J x * P r x := hself J r cJ cr
      _ = 0 := by simp [hPr]
  have hi : (∫ x in a..b, H x * r x) =
      -(∫ x in a..b, Hx x * (V x - P V x)) := by
    simp_rw [hr]
    exact periodic_skew_integral H (fun x => V x - P V x) Hx
      (fun x => Vx x - PVx x) a b hH (fun x => (hV x).sub (hPV x))
      cHx (cVx.sub cPVx) pH (by rw [pV, pPV])
  have hsub₁ : (∫ x in a..b, J x * r x - H x * r x) =
      (∫ x in a..b, J x * r x) - ∫ x in a..b, H x * r x :=
    intervalIntegral.integral_sub ((cJ.mul cr).intervalIntegrable a b)
      ((cH.mul cr).intervalIntegrable a b)
  have hsub₂ : (∫ x in a..b, Hx x * V x - Hx x * P V x) =
      (∫ x in a..b, Hx x * V x) - ∫ x in a..b, Hx x * P V x :=
    intervalIntegral.integral_sub ((cHx.mul cV).intervalIntegrable a b)
      ((cHx.mul cPV).intervalIntegrable a b)
  have hsub₃ : (∫ x in a..b, Hx x * V x - P Hx x * V x) =
      (∫ x in a..b, Hx x * V x) - ∫ x in a..b, P Hx x * V x :=
    intervalIntegral.integral_sub ((cHx.mul cV).intervalIntegrable a b)
      ((cPHx.mul cV).intervalIntegrable a b)
  calc
    _ = (∫ x in a..b, J x * r x) - ∫ x in a..b, H x * r x := by
      rw [← hsub₁]
      apply intervalIntegral.integral_congr
      intro x _
      ring
    _ = ∫ x in a..b, Hx x * (V x - P V x) := by rw [ho, hi]; ring
    _ = (∫ x in a..b, Hx x * V x) - ∫ x in a..b, Hx x * P V x := by
      rw [← hsub₂]
      apply intervalIntegral.integral_congr
      intro x _
      ring
    _ = (∫ x in a..b, Hx x * V x) - ∫ x in a..b, P Hx x * V x := by
      rw [hself Hx V cHx cV]
    _ = _ := by
      rw [← hsub₃]
      apply intervalIntegral.integral_congr
      intro x _
      ring

end

end KerrKoopman.ContinuumCalculus
