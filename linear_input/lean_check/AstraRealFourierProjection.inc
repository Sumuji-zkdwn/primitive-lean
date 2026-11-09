
/-!
# Strong convergence of the actual real Fourier projections

The proof uses actual complex Fourier approximation followed by real-part
recovery inside the explicit real trigonometric span. It does not assume
density of that span or convergence of the real projections.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter
open scoped Topology ComplexConjugate
open KerrKoopman.MaterialL2 KerrKoopman.RealFourierDerivative

namespace KerrKoopman.RealFourierProjection

theorem realPart_smul (c : ℂ) (f : FourierProjection.CircleL2) :
    realPart (c • f) = c.re • realPart f - c.im • imagPart f := by
  apply Lp.ext
  filter_upwards [realPart_ae (c • f), Lp.coeFn_smul c f,
    realPart_ae f, imagPart_ae f,
    Lp.coeFn_sub (c.re • realPart f) (c.im • imagPart f),
    Lp.coeFn_smul c.re (realPart f), Lp.coeFn_smul c.im (imagPart f)]
    with x ha hb hc hd he hf hg
  simp only [ha, hb, Pi.smul_apply, smul_eq_mul, Complex.mul_re,
    he, Pi.sub_apply, hf, hg, hc, hd]

theorem imagPart_smul (c : ℂ) (f : FourierProjection.CircleL2) :
    imagPart (c • f) = c.re • imagPart f + c.im • realPart f := by
  apply Lp.ext
  filter_upwards [imagPart_ae (c • f), Lp.coeFn_smul c f,
    realPart_ae f, imagPart_ae f,
    Lp.coeFn_add (c.re • imagPart f) (c.im • realPart f),
    Lp.coeFn_smul c.re (imagPart f), Lp.coeFn_smul c.im (realPart f)]
    with x ha hb hc hd he hf hg
  simp only [ha, hb, Pi.smul_apply, smul_eq_mul, Complex.mul_im,
    he, Pi.add_apply, hf, hg, hc, hd]

theorem realPart_basis_neg (k : ℕ) :
    realPart (FourierProjection.basis (-(k : ℤ))) = RealGalerkin.cosineL2 k := by
  apply Lp.ext
  filter_upwards [realPart_ae (FourierProjection.basis (-(k : ℤ))), basis_ae (-(k : ℤ)),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) AddCircle.haarAddCircle
      (RealGalerkin.cosine k)] with x hx hy hz
  change (RealGalerkin.cosineL2 k) x = (fourier (k : ℤ) x).re at hz
  simp only [hx, hy, hz, fourier_neg, Complex.conj_re]

theorem imagPart_basis_neg (k : ℕ) :
    imagPart (FourierProjection.basis (-(k : ℤ))) = -RealGalerkin.sineL2 k := by
  apply Lp.ext
  filter_upwards [imagPart_ae (FourierProjection.basis (-(k : ℤ))), basis_ae (-(k : ℤ)),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) AddCircle.haarAddCircle
      (RealGalerkin.sine k), Lp.coeFn_neg (RealGalerkin.sineL2 k)] with x hx hy hz hn
  change (RealGalerkin.sineL2 k) x = (fourier (k : ℤ) x).im at hz
  simp only [hx, hy, hn, Pi.neg_apply, hz, fourier_neg, Complex.conj_im]

/-- Real and imaginary parts of every complex bandlimited vector lie in the concrete real span. -/
theorem parts_mem (N : ℕ) {f : FourierProjection.CircleL2}
    (hf : f ∈ FourierProjection.bandlimited N) :
    realPart f ∈ RealGalerkin.space N ∧ imagPart f ∈ RealGalerkin.space N := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      change k ∈ FourierProjection.frequencies N at hk
      simp only [FourierProjection.frequencies, Finset.mem_Icc] at hk
      obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
      · have hn : n ≤ N := by omega
        rw [realPart_basis, imagPart_basis]
        exact ⟨cosine_mem N n hn, sine_mem N n hn⟩
      · have hn : n ≤ N := by omega
        rw [realPart_basis_neg, imagPart_basis_neg]
        exact ⟨cosine_mem N n hn, (RealGalerkin.space N).neg_mem (sine_mem N n hn)⟩
  | zero => simp only [map_zero]; exact ⟨(RealGalerkin.space N).zero_mem, (RealGalerkin.space N).zero_mem⟩
  | add x y hx hy ihx ihy =>
      simp only [map_add]
      exact ⟨(RealGalerkin.space N).add_mem ihx.1 ihy.1,
        (RealGalerkin.space N).add_mem ihx.2 ihy.2⟩
  | smul c x hx ih =>
      rw [realPart_smul, imagPart_smul]
      exact ⟨(RealGalerkin.space N).sub_mem
        ((RealGalerkin.space N).smul_mem c.re ih.1) ((RealGalerkin.space N).smul_mem c.im ih.2),
        (RealGalerkin.space N).add_mem
        ((RealGalerkin.space N).smul_mem c.re ih.2) ((RealGalerkin.space N).smul_mem c.im ih.1)⟩

theorem realPart_projection_mem (N : ℕ) (f : FourierProjection.CircleL2) :
    realPart (FourierProjection.projection N f) ∈ RealGalerkin.space N :=
  (parts_mem N (FourierProjection.projection_mem_bandlimited N f)).1

theorem contraction_error_of_fixed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E →L[ℝ] E) (hP : ∀ x, ‖P x‖ ≤ ‖x‖) (f g : E) (hfix : P g = g) :
    ‖P f - f‖ ≤ 2 * ‖f - g‖ := by
  calc
    ‖P f - f‖ = ‖P (f - g) - (f - g)‖ := by
          rw [map_sub, hfix]
          congr 1
          abel
    _ ≤ ‖P (f - g)‖ + ‖f - g‖ := norm_sub_le _ _
    _ ≤ ‖f - g‖ + ‖f - g‖ := add_le_add (hP (f - g)) le_rfl
    _ = 2 * ‖f - g‖ := by ring

theorem recovered_error_le (N : ℕ) (f : RealCircleL2) :
    ‖f - realPart (FourierProjection.projection N (complexify f))‖ ≤
      ‖FourierProjection.projection N (complexify f) - complexify f‖ := by
  have h := realPart_norm_le
    (FourierProjection.projection N (complexify f) - complexify f)
  rw [map_sub, realPart_complexify] at h
  rw [norm_sub_rev f (realPart (FourierProjection.projection N (complexify f)))]
  exact h

/-- A concrete quantitative comparison of real and complex cutoff errors. -/
theorem projection_error_le (N : ℕ) (f : RealCircleL2) :
    ‖RealGalerkin.projection N f - f‖ ≤
      2 * ‖FourierProjection.projection N (complexify f) - complexify f‖ := by
  exact (contraction_error_of_fixed (RealGalerkin.projection N)
    (RealGalerkin.projection_norm_le N) f
    (realPart (FourierProjection.projection N (complexify f)))
    (RealGalerkin.projection_eq_self N (realPart_projection_mem N (complexify f)))).trans
      (mul_le_mul_of_nonneg_left (recovered_error_le N f) (by norm_num))

/-- Strong L2 convergence for the constructed real trigonometric orthogonal projections. -/
theorem projection_tendsto (f : RealCircleL2) :
    Tendsto (fun N => RealGalerkin.projection N f) atTop (𝓝 f) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h : Tendsto
      (fun N => FourierProjection.projection N (complexify f) - complexify f)
      atTop (𝓝 0) := by
    simpa only [sub_self] using
      (FourierProjection.projection_tendsto (complexify f)).sub
        (tendsto_const_nhds (x := complexify f))
  have hnorm : Tendsto
      (fun N => 2 * ‖FourierProjection.projection N (complexify f) - complexify f‖)
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul h.norm
  exact squeeze_zero (fun N => norm_nonneg _) (fun N => projection_error_le N f) hnorm

/-- Uniform convergence on every compact set of real L2 fields, including compact time traces. -/
theorem projection_uniformOn_compact (K : Set RealCircleL2) (hK : IsCompact K) :
    TendstoUniformlyOn (fun N f => RealGalerkin.projection N f) id atTop K := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  have heq : Equicontinuous (fun N (f : K) => RealGalerkin.projection N (f : RealCircleL2)) := by
    apply Metric.equicontinuous_of_continuity_modulus id tendsto_id
    intro f g N
    simpa only [id_eq, NNReal.coe_one, one_mul, Subtype.dist_eq] using
      (RealGalerkin.projection_lipschitz N).dist_le_mul (f : RealCircleL2) (g : RealCircleL2)
  have hp : Tendsto (fun N (f : K) => RealGalerkin.projection N (f : RealCircleL2))
      atTop (𝓝 (fun f : K => (f : RealCircleL2))) :=
    tendsto_pi_nhds.mpr (fun f => projection_tendsto f)
  exact UniformFun.tendsto_iff_tendstoUniformly.mp
    ((heq.tendsto_uniformFun_iff_pi atTop (fun f : K => (f : RealCircleL2))).mpr hp)

end KerrKoopman.RealFourierProjection
