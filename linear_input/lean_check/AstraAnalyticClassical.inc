
/-! Globally continuous representatives of the actual analytic fields, and
an actual classical Kerr pair for the relative-energy theorem. -/
namespace KerrKoopman.AnalyticClassical
noncomputable section
set_option backward.isDefEq.respectTransparency false
open AnalyticFields AnalyticLift AnalyticAssembly AnalyticPDE
open Phase3WeightedRealDecode
open scoped Topology

def timeAt (p : Data) (t : ℝ) : Time p.T := Set.projIcc 0 p.T p.time_nonneg t

theorem timeAt_eq (p : Data) (t : Time p.T) : timeAt p t = t := by
  simp [timeAt, Set.projIcc_val]

theorem continuous_timeAt (p : Data) : Continuous (timeAt p) := continuous_projIcc (h := p.time_nonneg)

def E (p : Data) (t x : ℝ) : ℝ := electric p (timeAt p t) x
def H (p : Data) (t x : ℝ) : ℝ := magnetic p (timeAt p t) x
def D (p : Data) (t x : ℝ) : ℝ := displacementField p (timeAt p t) x
def Ex (p : Data) (t x : ℝ) : ℝ := realDerivative (width p.T) (eTrace p) (timeAt p t) x
def Hx (p : Data) (t x : ℝ) : ℝ := realDerivative (width p.T) (hTrace p) (timeAt p t) x

theorem E_eq (p : Data) (t : Time p.T) (x : ℝ) : E p t x = electric p t x := by rw [E, timeAt_eq]
theorem H_eq (p : Data) (t : Time p.T) (x : ℝ) : H p t x = magnetic p t x := by rw [H, timeAt_eq]
theorem D_eq (p : Data) (t : Time p.T) (x : ℝ) : D p t x = displacementField p t x := by rw [D, timeAt_eq]

theorem continuous_spaceTime (p : Data) :
    Continuous (fun q : ℝ × ℝ => (timeAt p q.1, q.2)) :=
  ((continuous_timeAt p).comp continuous_fst).prodMk continuous_snd

theorem continuous_E (p : Data) : Continuous (fun q : ℝ × ℝ => E p q.1 q.2) := by
  change Continuous ((fun q : Time p.T × ℝ => electric p q.1 q.2) ∘
    (fun q : ℝ × ℝ => (timeAt p q.1, q.2)))
  exact (fields_continuous p).1.comp (continuous_spaceTime p)

theorem continuous_H (p : Data) : Continuous (fun q : ℝ × ℝ => H p q.1 q.2) := by
  change Continuous ((fun q : Time p.T × ℝ => magnetic p q.1 q.2) ∘
    (fun q : ℝ × ℝ => (timeAt p q.1, q.2)))
  exact (fields_continuous p).2.2.comp (continuous_spaceTime p)

theorem continuous_D (p : Data) : Continuous (fun q : ℝ × ℝ => D p q.1 q.2) := by
  change Continuous ((fun q : Time p.T × ℝ => displacementField p q.1 q.2) ∘
    (fun q : ℝ × ℝ => (timeAt p q.1, q.2)))
  exact (fields_continuous p).2.1.comp (continuous_spaceTime p)

theorem continuous_Ex (p : Data) : Continuous (fun q : ℝ × ℝ => Ex p q.1 q.2) := by
  change Continuous ((fun q : Time p.T × ℝ => realDerivative (width p.T) (eTrace p) q.1 q.2) ∘
    (fun q : ℝ × ℝ => (timeAt p q.1, q.2)))
  exact (continuous_realDerivative (width p.T) (3 / 10) (by norm_num)
    (width_lower_bound p.T p.time_le) (eTrace p)).comp (continuous_spaceTime p)

theorem continuous_Hx (p : Data) : Continuous (fun q : ℝ × ℝ => Hx p q.1 q.2) := by
  change Continuous ((fun q : Time p.T × ℝ => realDerivative (width p.T) (hTrace p) q.1 q.2) ∘
    (fun q : ℝ × ℝ => (timeAt p q.1, q.2)))
  exact (continuous_realDerivative (width p.T) (3 / 10) (by norm_num)
    (width_lower_bound p.T p.time_le) (hTrace p)).comp (continuous_spaceTime p)

theorem E_space (p : Data) (t x : ℝ) : HasDerivAt (E p t) (Ex p t x) x :=
  (fields_spatial_derivatives p (timeAt p t) x).1

theorem H_space (p : Data) (t x : ℝ) : HasDerivAt (H p t) (Hx p t x) x :=
  (fields_spatial_derivatives p (timeAt p t) x).2.2

theorem E_time (p : Data) (t x : ℝ) (ht : t ∈ Set.Ioo 0 p.T) :
    HasDerivAt (fun s => E p s x) (-Hx p t x / (1 + E p t x ^ 2)) t := by
  have he : (fun s => E p s x) =ᶠ[𝓝 t] (fun s => electricExtension p s x) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    let st : Time p.T := ⟨s, hs.1.le, hs.2.le⟩
    exact (E_eq p st x).trans (electricExtension_eq p st x).symm
  have hd := (electric_time_derivative p t x ht).congr_of_eventuallyEq he
  have hc := timeAt_eq p (⟨t, ht.1.le, ht.2.le⟩ : Time p.T)
  simpa only [E, Hx, hc] using hd

theorem H_time (p : Data) (t x : ℝ) (ht : t ∈ Set.Ioo 0 p.T) :
    HasDerivAt (fun s => H p s x) (-Ex p t x) t := by
  have he : (fun s => H p s x) =ᶠ[𝓝 t] (fun s => magneticExtension p s x) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    let st : Time p.T := ⟨s, hs.1.le, hs.2.le⟩
    exact (H_eq p st x).trans (magneticExtension_eq p st x).symm
  have hd := (magnetic_time_derivative p t x ht).congr_of_eventuallyEq he
  have hc := timeAt_eq p (⟨t, ht.1.le, ht.2.le⟩ : Time p.T)
  simpa only [Ex, hc] using hd

theorem E_endpoint (p : Data) (t : ℝ) : E p t IntervalFourier.period = E p t 0 := by
  simpa only [E, IntervalFourier.period, zero_add] using
    (fields_periodic p (timeAt p t)).1 0

theorem H_endpoint (p : Data) (t : ℝ) : H p t IntervalFourier.period = H p t 0 := by
  simpa only [H, IntervalFourier.period, zero_add] using
    (fields_periodic p (timeAt p t)).2.2 0

theorem Hx_bound (p : Data) (t x : ℝ) : |Hx p t x| ≤ 1 := by
  have h := realDerivative_norm_le (width p.T) (3 / 10) (by norm_num)
    (width_lower_bound p.T p.time_le) (hTrace p) (timeAt p t) x
  have hh := hTrace_bound p
  have he : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hr : 0 ≤ Real.exp (-1) / (3 / 10) := by positivity
  have hm := mul_le_mul_of_nonneg_left hh hr
  change |Hx p t x| ≤ 1
  rw [Real.norm_eq_abs] at h
  change |Hx p t x| ≤ _ at h
  nlinarith [Real.exp_pos (-1)]

theorem continuous_E_slice (p : Data) (t : ℝ) : Continuous (E p t) := by
  change Continuous ((fun q : ℝ × ℝ => E p q.1 q.2) ∘ (fun x : ℝ => (t, x)))
  exact (continuous_E p).comp
    (show Continuous (fun x : ℝ => (t, x)) from continuous_const.prodMk continuous_id)

theorem continuous_H_slice (p : Data) (t : ℝ) : Continuous (H p t) := by
  change Continuous ((fun q : ℝ × ℝ => H p q.1 q.2) ∘ (fun x : ℝ => (t, x)))
  exact (continuous_H p).comp
    (show Continuous (fun x : ℝ => (t, x)) from continuous_const.prodMk continuous_id)

theorem continuous_Ex_slice (p : Data) (t : ℝ) : Continuous (Ex p t) := by
  change Continuous ((fun q : ℝ × ℝ => Ex p q.1 q.2) ∘ (fun x : ℝ => (t, x)))
  exact (continuous_Ex p).comp
    (show Continuous (fun x : ℝ => (t, x)) from continuous_const.prodMk continuous_id)

theorem continuous_Hx_slice (p : Data) (t : ℝ) : Continuous (Hx p t) := by
  change Continuous ((fun q : ℝ × ℝ => Hx p q.1 q.2) ∘ (fun x : ℝ => (t, x)))
  exact (continuous_Hx p).comp
    (show Continuous (fun x : ℝ => (t, x)) from continuous_const.prodMk continuous_id)

/-- An actual pair with zero comparison residual; Galerkin comparison later
replaces its V,J components, retaining the constructed analytic E,H fields. -/
def pair (p : Data) : ContinuumRelative.ClassicalKerrPair 0 IntervalFourier.period (Set.Ioo 0 p.T) where
  E := E p
  H := H p
  V := E p
  J := H p
  Ex := Ex p
  Hx := Hx p
  Vx := Ex p
  Jx := Hx p
  residual := fun _ _ => 0
  continuous_E t := continuous_E_slice p t
  continuous_H t := continuous_H_slice p t
  continuous_V t := continuous_E_slice p t
  continuous_J t := continuous_H_slice p t
  continuous_Ex t := continuous_Ex_slice p t
  continuous_Hx t := continuous_Hx_slice p t
  continuous_Vx t := continuous_Ex_slice p t
  continuous_Jx t := continuous_Hx_slice p t
  continuous_residual _ := continuous_const
  spatial_E t _ x := E_space p t x
  spatial_H t _ x := H_space p t x
  spatial_V t _ x := E_space p t x
  spatial_J t _ x := H_space p t x
  time_E t ht x := E_time p t x ht
  time_H t ht x := H_time p t x ht
  time_V t ht x := E_time p t x ht
  time_J t ht x := by simpa only [add_zero] using H_time p t x ht
  periodic_E t _ := E_endpoint p t
  periodic_H t _ := H_endpoint p t
  periodic_V t _ := E_endpoint p t
  periodic_J t _ := H_endpoint p t

end
end KerrKoopman.AnalyticClassical
