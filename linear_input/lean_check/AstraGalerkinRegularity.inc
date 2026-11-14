
/-! Joint continuity supplies actual energy continuity and compact domination of the computed rate. -/

namespace KerrKoopman.GalerkinClassical

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set FiniteRepresentatives RealFourierDerivative ExplicitMaterial
open scoped Interval

theorem lift_joint_of_continuous (N : ℕ) (z : ℝ → RealGalerkin.space N) (hz : Continuous z) :
    Continuous (fun p : ℝ × ℝ => lift N (z p.1) p.2) := by
  have hf : Continuous (fun p : ℝ × ℝ => representative N (z p.1)) :=
    (representative N).continuous.comp (hz.comp continuous_fst)
  have hx : Continuous (fun p : ℝ × ℝ => (p.2 : Circle)) :=
    (AddCircle.continuous_mk' (2*Real.pi)).comp continuous_snd
  exact continuous_eval.comp (hf.prodMk hx)

theorem flow_time_continuous (N : ℕ) (z : GalerkinFlow.State N) :
    Continuous (fun t => GalerkinFlow.flow N t z) :=
  continuous_iff_continuousAt.mpr (fun t => (GalerkinFlow.hasDerivAt_flow N t z).continuousAt)

theorem flow_fst_continuous (N : ℕ) (z : GalerkinFlow.State N) :
    Continuous (fun t => (GalerkinFlow.flow N t z).fst) :=
  (WithLp.fstL 2 ℝ (RealGalerkin.space N) (RealGalerkin.space N)).continuous.comp
    (flow_time_continuous N z)

theorem flow_snd_continuous (N : ℕ) (z : GalerkinFlow.State N) :
    Continuous (fun t => (GalerkinFlow.flow N t z).snd) :=
  (WithLp.sndL 2 ℝ (RealGalerkin.space N) (RealGalerkin.space N)).continuous.comp
    (flow_time_continuous N z)

theorem displacement_joint (N : ℕ) (z : GalerkinFlow.State N) :
    Continuous (fun p : ℝ × ℝ => displacement N z p.1 p.2) :=
  lift_joint_of_continuous N _ (flow_fst_continuous N z)

theorem magnetic_joint (N : ℕ) (z : GalerkinFlow.State N) :
    Continuous (fun p : ℝ × ℝ => magnetic N z p.1 p.2) :=
  lift_joint_of_continuous N _ (flow_snd_continuous N z)

theorem electric_joint (N : ℕ) (z : GalerkinFlow.State N) :
    Continuous (fun p : ℝ × ℝ => electric N z p.1 p.2) :=
  electricOfDisplacement_lipschitz.continuous.comp (displacement_joint N z)

theorem magnetic_deriv_joint (N : ℕ) (z : GalerkinFlow.State N) :
    Continuous (fun p : ℝ × ℝ => deriv (magnetic N z p.1) p.2) := by
  have h := lift_joint_of_continuous N _ ((finiteDerivative N).continuous.comp (flow_snd_continuous N z))
  simpa only [(magnetic_space N z _ _).deriv, Function.comp_def] using h

theorem electric_deriv_joint (N : ℕ) (z : GalerkinFlow.State N) :
    Continuous (fun p : ℝ × ℝ => deriv (electric N z p.1) p.2) := by
  have hD := lift_joint_of_continuous N _ ((finiteDerivative N).continuous.comp (flow_fst_continuous N z))
  have hE := electric_joint N z
  have hid : (fun p : ℝ × ℝ => deriv (electric N z p.1) p.2) =
      (fun p => 1/(1+(electric N z p.1 p.2)^2)*
        lift N (finiteDerivative N (GalerkinFlow.flow N p.1 z).fst) p.2) := by
    funext p
    exact ((hasDerivAt_electricOfDisplacement (displacement N z p.1 p.2)).comp p.2
      (displacement_space N z p.1 p.2)).deriv
  rw [hid]
  have hn : ∀ p : ℝ × ℝ, 1+(electric N z p.1 p.2)^2 ≠ 0 := fun p => by positivity
  fun_prop (disch := assumption)

theorem projected_electric_deriv_joint (N : ℕ) (z : GalerkinFlow.State N) :
    Continuous (fun p : ℝ × ℝ => deriv (IntervalFourier.projection N (electric N z p.1)) p.2) := by
  have hG := (RealGalerkin.projectedMaterial_lipschitz N).continuous.comp (flow_fst_continuous N z)
  have h := lift_joint_of_continuous N _ ((finiteDerivative N).continuous.comp hG)
  have hid (t : ℝ) : IntervalFourier.projection N (electric N z t) =
      lift N (RealGalerkin.projectedMaterial N (GalerkinFlow.flow N t z).fst) :=
    (lift_projectedMaterial N _).symm
  simp_rw [hid, lift_deriv]
  exact h

theorem relative_density_joint {s : Set ℝ}
    (base : ContinuumRelative.ClassicalKerrPair 0 IntervalFourier.period s)
    (N : ℕ) (z : GalerkinFlow.State N)
    (hE : Continuous (fun p : ℝ × ℝ => base.E p.1 p.2))
    (hH : Continuous (fun p : ℝ × ℝ => base.H p.1 p.2)) :
    Continuous (fun p : ℝ × ℝ => (withGalerkin base N z).density p.1 p.2) := by
  have hV := electric_joint N z
  have hJ := magnetic_joint N z
  change Continuous (fun p : ℝ × ℝ => RelativeDynamics.relativeDensity
    (base.E p.1 p.2) (base.H p.1 p.2) (electric N z p.1 p.2) (magnetic N z p.1 p.2))
  unfold RelativeDynamics.relativeDensity RelativeEnergy.electricGap FiniteEnergy.density Riccati.constitutive
  fun_prop

theorem relative_rate_joint {s : Set ℝ}
    (base : ContinuumRelative.ClassicalKerrPair 0 IntervalFourier.period s)
    (N : ℕ) (z : GalerkinFlow.State N)
    (hE : Continuous (fun p : ℝ × ℝ => base.E p.1 p.2))
    (hH : Continuous (fun p : ℝ × ℝ => base.H p.1 p.2))
    (hEx : Continuous (fun p : ℝ × ℝ => base.Ex p.1 p.2))
    (hHx : Continuous (fun p : ℝ × ℝ => base.Hx p.1 p.2)) :
    Continuous (fun p : ℝ × ℝ => (withGalerkin base N z).rate p.1 p.2) := by
  have hV := electric_joint N z
  have hJ := magnetic_joint N z
  have hVx := electric_deriv_joint N z
  have hJx := magnetic_deriv_joint N z
  have hPVx := projected_electric_deriv_joint N z
  change Continuous (fun p : ℝ × ℝ => ContinuumRelative.densityRate
    (base.E p.1 p.2) (base.H p.1 p.2) (electric N z p.1 p.2) (magnetic N z p.1 p.2)
    (base.Ex p.1 p.2) (base.Hx p.1 p.2) (deriv (electric N z p.1) p.2)
    (deriv (magnetic N z p.1) p.2) (deriv (electric N z p.1) p.2-
      deriv (IntervalFourier.projection N (electric N z p.1)) p.2))
  unfold ContinuumRelative.densityRate Riccati.constitutive
  have hnE : ∀ p : ℝ × ℝ, 1+(base.E p.1 p.2)^2 ≠ 0 := fun p => by positivity
  have hnV : ∀ p : ℝ × ℝ, 1+(electric N z p.1 p.2)^2 ≠ 0 := fun p => by positivity
  fun_prop (disch := assumption)

theorem normalized_energy_continuous {s : Set ℝ}
    (base : ContinuumRelative.ClassicalKerrPair 0 IntervalFourier.period s)
    (N : ℕ) (z : GalerkinFlow.State N)
    (hE : Continuous (fun p : ℝ × ℝ => base.E p.1 p.2))
    (hH : Continuous (fun p : ℝ × ℝ => base.H p.1 p.2)) :
    Continuous (ContinuumGalerkin.ClassicalKerrPair.normalizedEnergy (withGalerkin base N z)) := by
  have h := continuous_parametric_integral_of_continuous
    (μ := volume) (f := (withGalerkin base N z).density) (relative_density_joint base N z hE hH)
    (isCompact_Icc (a := (0 : ℝ)) (b := IntervalFourier.period))
  have hp : (0 : ℝ) ≤ IntervalFourier.period := by unfold IntervalFourier.period; positivity
  have he : (fun t => ∫ x in Icc 0 IntervalFourier.period,
      (withGalerkin base N z).density t x) = (withGalerkin base N z).energy := by
    funext t
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hp]
    rfl
  rw [he] at h
  exact h.div_const _

/-- Compact spacetime continuity supplies the domination used for differentiating the energy. -/
theorem exists_rate_bound {s : Set ℝ}
    (base : ContinuumRelative.ClassicalKerrPair 0 IntervalFourier.period s)
    (N : ℕ) (z : GalerkinFlow.State N) (T : ℝ)
    (hE : Continuous (fun p : ℝ × ℝ => base.E p.1 p.2))
    (hH : Continuous (fun p : ℝ × ℝ => base.H p.1 p.2))
    (hEx : Continuous (fun p : ℝ × ℝ => base.Ex p.1 p.2))
    (hHx : Continuous (fun p : ℝ × ℝ => base.Hx p.1 p.2)) :
    ∃ bound : ℝ → ℝ, IntervalIntegrable bound volume 0 IntervalFourier.period ∧
      ∀ x ∈ uIcc 0 IntervalFourier.period, ∀ q ∈ Ioo 0 T,
        |(withGalerkin base N z).rate q x| ≤ bound x := by
  have hc := relative_rate_joint base N z hE hH hEx hHx
  obtain ⟨M,hM⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := T)).prod
    (isCompact_Icc (a := (0 : ℝ)) (b := IntervalFourier.period))).bddAbove_image hc.norm.continuousOn
  refine ⟨fun _ => M, continuous_const.intervalIntegrable _ _, ?_⟩
  intro x hx q hq
  have hp : (0 : ℝ) ≤ IntervalFourier.period := by unfold IntervalFourier.period; positivity
  rw [uIcc_of_le hp] at hx
  have hm := hM (mem_image_of_mem _ (mk_mem_prod (Ioo_subset_Icc_self hq) hx))
  simpa only [Real.norm_eq_abs] using hm

end
end KerrKoopman.GalerkinClassical
