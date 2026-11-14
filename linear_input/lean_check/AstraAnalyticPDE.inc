
/-! The actual all-mode fixed point satisfies the Kerr Maxwell equations in
physical time and takes the supplied initial Fourier coefficients. -/

namespace KerrKoopman.AnalyticPDE
noncomputable section
set_option backward.isDefEq.respectTransparency false
open AnalyticLift AnalyticAssembly AnalyticFields AnalyticTransport
open Phase3WeightedRealDecode Phase3WeightedDerivative
open scoped Topology

abbrev speed : ℝ := 1 / Real.sqrt 2

theorem speed_sq : speed ^ 2 = 1 / 2 := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

def branchTrace (p : Data) (b : Bool) : Scalar p.T := branch p.T b (branches p)
def branchSpeed (b : Bool) : ℝ := if b then speed else -speed

theorem branch_mild (p : Data) (b : Bool) :
    MildCoefficients p.T p.time_nonneg (branchSpeed b)
      (fun k => component b (p.initial k)) (branchTrace p b) (nTrace p) := by
  intro k t
  have he := mildSolution_equation p.T p.time_nonneg p.time_le p.initial p.initial_bound
  cases b
  · have h := congrArg (fun z : Branches p.T => (z k t).2) he
    change waveFactor p.T 1 speed k (-1) t * (p.initial k).2 +
      AnalyticFourierDuhamel.mode p.T p.time_nonneg 1 (-speed) _ k (nTrace p k) t =
        branchTrace p false k t at h
    change branchTrace p false k t = waveFactor p.T 1 (-speed) k 1 t * (p.initial k).2 + _
    have hw : waveFactor p.T 1 (-speed) k 1 t = waveFactor p.T 1 speed k (-1) t := by
      change (Real.exp (-1 * (t : ℝ) * |(k : ℝ)|) : ℂ) *
        Complex.exp (((-1 * (-speed) * (k : ℝ) * (t : ℝ) : ℝ) : ℂ) * Complex.I) =
        (Real.exp (-1 * (t : ℝ) * |(k : ℝ)|) : ℂ) *
        Complex.exp (((-(-1) * speed * (k : ℝ) * (t : ℝ) : ℝ) : ℂ) * Complex.I)
      simp
    rw [hw]
    exact h.symm
  · have h := congrArg (fun z : Branches p.T => (z k t).1) he
    exact h.symm

def branchExtension (p : Data) (b : Bool) (t x : ℝ) : ℝ :=
  realExtension p.T p.time_nonneg (branchTrace p b) t x

def branchX (p : Data) (b : Bool) (t : Time p.T) (x : ℝ) : ℝ :=
  realDerivative (width p.T) (branchTrace p b) t x

def nonlinearX (p : Data) (t : Time p.T) (x : ℝ) : ℝ :=
  realDerivative (width p.T) (nTrace p) t x

theorem branchExtension_eq (p : Data) (b : Bool) (t : Time p.T) (x : ℝ) :
    branchExtension p b t x = decode p (branchTrace p b) t x := by
  rw [decode_eq]
  exact realExtension_eq p.T p.time_nonneg _ t x

theorem branch_time_derivative (p : Data) (b : Bool) (t x : ℝ) (ht : t ∈ Set.Ioo 0 p.T) :
    HasDerivAt (fun s => branchExtension p b s x)
      (-branchSpeed b * branchX p b ⟨t, ht.1.le, ht.2.le⟩ x -
        nonlinearX p ⟨t, ht.1.le, ht.2.le⟩ x) t :=
  realExtension_hasDerivAt p.T p.time_nonneg p.time_le (branchSpeed b)
    (fun k => component b (p.initial k)) (branchTrace p b) (nTrace p) (branch_mild p b) t x ht

theorem branch_space_derivative (p : Data) (b : Bool) (t : Time p.T) (x : ℝ) :
    HasDerivAt (fun y => decode p (branchTrace p b) t y) (branchX p b t x) x := by
  have he : (fun y => decode p (branchTrace p b) t y) =
      realDecode (width p.T) (branchTrace p b) t := funext (decode_eq p _ t)
  rw [he]
  exact hasDerivAt_realDecode _ (3 / 10) (by norm_num) (width_lower_bound p.T p.time_le) _ t x

theorem dTrace_eq (p : Data) :
    dTrace p = speed • (branchTrace p true - branchTrace p false) := by
  ext k t
  rfl

theorem displacementField_eq (p : Data) (t : Time p.T) (x : ℝ) :
    displacementField p t x = 4 / 3 + speed *
      (decode p (branchTrace p true) t x - decode p (branchTrace p false) t x) := by
  unfold displacementField decode
  rw [dTrace_eq, map_smul, map_sub, smul_eq_mul]

theorem magnetic_eq (p : Data) (t : Time p.T) (x : ℝ) :
    magnetic p t x = 3 / 10 + (1 / 2) *
      (decode p (branchTrace p true) t x + decode p (branchTrace p false) t x) := by
  unfold magnetic hTrace decode
  rw [map_smul, map_add, smul_eq_mul]
  rfl

theorem displacementX_eq (p : Data) (t : Time p.T) (x : ℝ) :
    realDerivative (width p.T) (dTrace p) t x = speed * (branchX p true t x - branchX p false t x) := by
  have hd := (((branch_space_derivative p true t x).sub
    (branch_space_derivative p false t x)).const_mul speed).const_add (4 / 3)
  have he : displacementField p t = fun y => 4 / 3 + speed *
      (decode p (branchTrace p true) t y - decode p (branchTrace p false) t y) :=
    funext (displacementField_eq p t)
  simp only [Pi.sub_apply] at hd
  rw [← he] at hd
  exact (fields_spatial_derivatives p t x).2.1.unique hd

theorem magneticX_eq (p : Data) (t : Time p.T) (x : ℝ) :
    realDerivative (width p.T) (hTrace p) t x = (1 / 2) * (branchX p true t x + branchX p false t x) := by
  have hd := (((branch_space_derivative p true t x).add
    (branch_space_derivative p false t x)).const_mul (1 / 2)).const_add (3 / 10)
  have he : magnetic p t = fun y => 3 / 10 + (1 / 2) *
      (decode p (branchTrace p true) t y + decode p (branchTrace p false) t y) :=
    funext (magnetic_eq p t)
  simp only [Pi.add_apply] at hd
  rw [← he] at hd
  exact (fields_spatial_derivatives p t x).2.2.unique hd

theorem electric_eq (p : Data) (t : Time p.T) (x : ℝ) :
    electric p t x = 1 + decode p (nTrace p) t x + (1 / 2) * decode p (dTrace p) t x := by
  rw [nonlinear_identity]
  unfold AnalyticFields.electric
  ring

theorem electricX_eq (p : Data) (t : Time p.T) (x : ℝ) :
    realDerivative (width p.T) (eTrace p) t x = nonlinearX p t x +
      (1 / 2) * realDerivative (width p.T) (dTrace p) t x := by
  have hn : HasDerivAt (fun y => decode p (nTrace p) t y) (nonlinearX p t x) x := by
    have he : (fun y => decode p (nTrace p) t y) = realDecode (width p.T) (nTrace p) t :=
      funext (decode_eq p _ t)
    rw [he]
    exact hasDerivAt_realDecode _ (3 / 10) (by norm_num) (width_lower_bound p.T p.time_le) _ t x
  have hd : HasDerivAt (fun y => decode p (dTrace p) t y)
      (realDerivative (width p.T) (dTrace p) t x) x := by
    have he : (fun y => decode p (dTrace p) t y) = realDecode (width p.T) (dTrace p) t :=
      funext (decode_eq p _ t)
    rw [he]
    exact hasDerivAt_realDecode _ (3 / 10) (by norm_num) (width_lower_bound p.T p.time_le) _ t x
  have he : electric p t = fun y => 1 + decode p (nTrace p) t y + (1 / 2) * decode p (dTrace p) t y :=
    funext (electric_eq p t)
  have h := (hn.const_add 1).add (hd.const_mul (1 / 2))
  change HasDerivAt (fun y => 1 + decode p (nTrace p) t y + (1 / 2) * decode p (dTrace p) t y)
    (nonlinearX p t x + (1 / 2) * realDerivative (width p.T) (dTrace p) t x) x at h
  rw [← he] at h
  exact (fields_spatial_derivatives p t x).1.unique h

def displacementExtension (p : Data) (t x : ℝ) : ℝ :=
  4 / 3 + speed * (branchExtension p true t x - branchExtension p false t x)

def magneticExtension (p : Data) (t x : ℝ) : ℝ :=
  3 / 10 + (1 / 2) * (branchExtension p true t x + branchExtension p false t x)

def electricExtension (p : Data) (t x : ℝ) : ℝ :=
  PrimitiveConstitutive.materialInverse (displacementExtension p t x)

theorem displacementExtension_eq (p : Data) (t : Time p.T) (x : ℝ) :
    displacementExtension p t x = displacementField p t x := by
  rw [displacementField_eq, displacementExtension, branchExtension_eq, branchExtension_eq]

theorem magneticExtension_eq (p : Data) (t : Time p.T) (x : ℝ) :
    magneticExtension p t x = magnetic p t x := by
  rw [magnetic_eq, magneticExtension, branchExtension_eq, branchExtension_eq]

theorem electricExtension_eq (p : Data) (t : Time p.T) (x : ℝ) :
    electricExtension p t x = electric p t x := by
  unfold electricExtension
  rw [displacementExtension_eq, material_identity]
  exact PrimitiveConstitutive.materialInverse_constitutive _

/-- Actual first Maxwell equation for the constructed infinite-mode solution. -/
theorem displacement_time_derivative (p : Data) (t x : ℝ) (ht : t ∈ Set.Ioo 0 p.T) :
    HasDerivAt (fun s => displacementExtension p s x)
      (-realDerivative (width p.T) (hTrace p) ⟨t, ht.1.le, ht.2.le⟩ x) t := by
  have hd := (((branch_time_derivative p true t x ht).sub
    (branch_time_derivative p false t x ht)).const_mul speed).const_add (4 / 3)
  convert hd using 1
  · rfl
  · rw [magneticX_eq]
    simp only [branchSpeed, Bool.false_eq_true, ↓reduceIte, neg_neg]
    linear_combination (branchX p true ⟨t, ht.1.le, ht.2.le⟩ x +
      branchX p false ⟨t, ht.1.le, ht.2.le⟩ x) * speed_sq

/-- Actual second Maxwell equation for the constructed infinite-mode solution. -/
theorem magnetic_time_derivative (p : Data) (t x : ℝ) (ht : t ∈ Set.Ioo 0 p.T) :
    HasDerivAt (fun s => magneticExtension p s x)
      (-realDerivative (width p.T) (eTrace p) ⟨t, ht.1.le, ht.2.le⟩ x) t := by
  have hd := (((branch_time_derivative p true t x ht).add
    (branch_time_derivative p false t x ht)).const_mul (1 / 2)).const_add (3 / 10)
  convert hd using 1
  · rfl
  · rw [electricX_eq, displacementX_eq]
    simp only [branchSpeed, Bool.false_eq_true, ↓reduceIte, neg_neg]
    ring

theorem electric_time_derivative (p : Data) (t x : ℝ) (ht : t ∈ Set.Ioo 0 p.T) :
    HasDerivAt (fun s => electricExtension p s x)
      (-realDerivative (width p.T) (hTrace p) ⟨t, ht.1.le, ht.2.le⟩ x /
        (1 + electric p ⟨t, ht.1.le, ht.2.le⟩ x ^ 2)) t := by
  have h := (ExplicitMaterial.hasDerivAt_materialInverse (displacementExtension p t x)).comp t
    (displacement_time_derivative p t x ht)
  change HasDerivAt (fun s => electricExtension p s x) _ _ at h
  rw [show PrimitiveConstitutive.materialInverse (displacementExtension p t x) =
    electric p ⟨t, ht.1.le, ht.2.le⟩ x from electricExtension_eq p ⟨t, ht.1.le, ht.2.le⟩ x] at h
  convert h using 1
  ring

/-- Both equations stated directly with derivatives of the restored physical fields. -/
theorem maxwell_equations (p : Data) (t x : ℝ) (ht : t ∈ Set.Ioo 0 p.T) :
    deriv (fun s => displacementExtension p s x) t =
      -deriv (magnetic p ⟨t, ht.1.le, ht.2.le⟩) x ∧
    deriv (fun s => magneticExtension p s x) t =
      -deriv (electric p ⟨t, ht.1.le, ht.2.le⟩) x := by
  rw [(displacement_time_derivative p t x ht).deriv,
    (magnetic_time_derivative p t x ht).deriv,
    (fields_spatial_derivatives p ⟨t, ht.1.le, ht.2.le⟩ x).2.2.deriv,
    (fields_spatial_derivatives p ⟨t, ht.1.le, ht.2.le⟩ x).1.deriv]
  exact ⟨rfl, rfl⟩

end
end KerrKoopman.AnalyticPDE
