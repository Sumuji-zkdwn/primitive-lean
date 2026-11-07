import PADFourLayerCalibration

/-!
# Three-probe calibrated finite PAD model: algebraic determinant and counterexamples

Additive sidecar to PR #101. Original PADFourLayer / Calibration proofs unchanged.
All formal statements here concern rational polynomial data only.
The common toy calibration s = u^alpha, real logarithmic derivatives, and
physical PAD mapping are NOT asserted as Lean theorems in this module.
-/

namespace PADFourLayerThreeProbe

open PADFourLayer

/-- Response row in (p2,p3) coordinates after mass/mean are fixed. -/
def coefA (x : ℚ) : ℚ := (x-1)^2
def coefB (x : ℚ) : ℚ := (x-1)^2 * (x+2)

/-- Symbolic three-by-three Jacobian determinant with a freely specified
nuisance-parameter velocity `v_i` at each probe. -/
def jacDet (s t u vs vt vu : ℚ) : ℚ :=
  coefA s * (coefB t * vu - coefB u * vt) -
  coefB s * (coefA t * vu - coefA u * vt) +
  vs * (coefA t * coefB u - coefA u * coefB t)

/-- Denominator-free exact determinant formula. Does not use transcendental
logarithms or any assumption about how the nuisance velocities were obtained. -/
theorem jacDet_closed (s t u vs vt vu : ℚ) :
    jacDet s t u vs vt vu =
      coefA s * coefA t * (t-s) * vu -
      coefA s * coefA u * (u-s) * vt +
      coefA t * coefA u * (u-t) * vs := by
  unfold jacDet coefA coefB
  ring

/-- A directly checkable sufficient nondegeneracy criterion for the symbolic
Jacobian, derived from the preceding exact formula. -/
theorem jacDet_nonzero_of_cross (s t u vs vt vu : ℚ)
    (h : coefA s * coefA t * (t-s) * vu -
      coefA s * coefA u * (u-s) * vt +
      coefA t * coefA u * (u-t) * vs ≠ 0) :
    jacDet s t u vs vt vu ≠ 0 := by
  rw [jacDet_closed]
  exact h

/-- Repeating a probe with the same nuisance response cannot add rank. -/
theorem repeated_probe (s u vs vu : ℚ) :
    jacDet s s u vs vs vu = 0 := by
  unfold jacDet coefA coefB
  ring

/-- A probe at s=1 has a zero Jacobian row if its nuisance velocity is zero
(as with u=1 and s=u^alpha). -/
theorem unit_probe (t u vt vu : ℚ) :
    jacDet 1 t u 0 vt vu = 0 := by
  simp [jacDet, coefA, coefB]

/-- Strictly positive rational profiles with mass 1, mean 3/2 that agree at
three distinct nominal probes after changing a *common* alpha from 1 to 4/3.
At nominal u_i = t_i^3, the two actual probe grids are t_i^3 and t_i^4. -/
def tripleP : Profile :=
  ⟨30373/121700, 6137/60850, 66883/121700, 1/10⟩
def tripleQ : Profile :=
  ⟨760623/3042500, 249697/760625, 56861/608500, 249696/760625⟩

theorem triple_masses : mass tripleP = 1 ∧ mass tripleQ = 1 := by
  norm_num [mass, tripleP, tripleQ]

theorem triple_means : mean tripleP = 3/2 ∧ mean tripleQ = 3/2 := by
  norm_num [mean, tripleP, tripleQ]

theorem triple_positive :
    0 < tripleP.p0 ∧ 0 < tripleP.p1 ∧
    0 < tripleP.p2 ∧ 0 < tripleP.p3 ∧
    0 < tripleQ.p0 ∧ 0 < tripleQ.p1 ∧
    0 < tripleQ.p2 ∧ 0 < tripleQ.p3 := by
  norm_num [tripleP, tripleQ]

theorem triple_distinct : tripleP ≠ tripleQ := by
  intro h
  have h3 := congrArg Profile.p3 h
  norm_num [tripleP, tripleQ] at h3

/-- Exact three-probe ambiguity: all three readings agree despite different
strictly positive profiles and different common calibrated coordinates. -/
theorem triple_ambiguity :
    response (1/64) tripleP = response (1/256) tripleQ ∧
    response (1/27) tripleP = response (1/81) tripleQ ∧
    response (1/8) tripleP = response (1/16) tripleQ := by
  norm_num [response, tripleP, tripleQ]

/-- Polynomial part of alpha-derivative for u=r^k:
actual derivative is `log r * scaleDeriv p u k` at alpha=1. -/
def scaleDeriv (p : Profile) (u k : ℚ) : ℚ :=
  k*u*(p.p1 + 2*p.p2*u + 3*p.p3*u^2)

/-- A *strictly positive* rational profile at which the exact symbolic
three-probe Jacobian has a zero determinant. At nominal probes
r^3,r^2,r for r=1/4, the omitted common factor is log(1/4). -/
def singularP : Profile :=
  ⟨5093/40320, 10027/20160, 5093/40320, 1/4⟩

theorem singular_positive :
    0 < singularP.p0 ∧ 0 < singularP.p1 ∧
    0 < singularP.p2 ∧ 0 < singularP.p3 ∧
    mass singularP = 1 ∧ mean singularP = 3/2 := by
  norm_num [singularP, mass, mean]

theorem singular_jacobian :
    jacDet (1/64) (1/16) (1/4)
      (scaleDeriv singularP (1/64) 3)
      (scaleDeriv singularP (1/16) 2)
      (scaleDeriv singularP (1/4) 1) = 0 := by
  norm_num [jacDet, coefA, coefB, scaleDeriv, singularP]

/-- At the same three nominal probes, a uniform profile has a nonzero
symbolic three-probe determinant, confirming that degeneracy is not forced
by the probe grid alone. -/
def uniformP : Profile := ⟨1/4,1/4,1/4,1/4⟩

theorem regular_jacobian :
    jacDet (1/64) (1/16) (1/4)
      (scaleDeriv uniformP (1/64) 3)
      (scaleDeriv uniformP (1/16) 2)
      (scaleDeriv uniformP (1/4) 1) ≠ 0 := by
  norm_num [jacDet, coefA, coefB, scaleDeriv, uniformP]

end PADFourLayerThreeProbe
