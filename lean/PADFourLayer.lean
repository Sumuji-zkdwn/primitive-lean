import Mathlib

/-!
# Four-layer PAD observation: exact finite identifiability

This is an idealized forward model, NOT experimental PAD data or a proof of
full three-dimensional electron transport. A calibrated experiment must
supply the energy-to-s mapping and energy-dependent escape weights.

response s p = sum_j p_j * s^j is the normalized P2 response for
four fixed scattering counts with a spherical rotationally symmetric
scattering kernel; under additional Poisson assumptions it can also
model four depth levels using s = exp(-lambda*(1-c2)).
-/

namespace PADFourLayer

structure Profile where
  p0 : ℚ
  p1 : ℚ
  p2 : ℚ
  p3 : ℚ
  deriving Repr, DecidableEq

def mass (p : Profile) : ℚ := p.p0 + p.p1 + p.p2 + p.p3

def mean (p : Profile) : ℚ := p.p1 + 2*p.p2 + 3*p.p3

def response (s : ℚ) (p : Profile) : ℚ :=
  p.p0 + p.p1*s + p.p2*s^2 + p.p3*s^3

def plus : Profile := ⟨11/60, 7/15, 1/60, 1/3⟩
def minus : Profile := ⟨19/60, 1/30, 29/60, 1/6⟩

theorem witness_distinct : plus ≠ minus := by decide

theorem witness_mass : mass plus = 1 ∧ mass minus = 1 := by
  norm_num [mass, plus, minus]

theorem witness_mean : mean plus = 3/2 ∧ mean minus = 3/2 := by
  norm_num [mean, plus, minus]

theorem witness_first_probe :
    response (4/5) plus = 369/500 ∧
    response (4/5) minus = 369/500 := by
  norm_num [response, plus, minus]

theorem witness_second_probe :
    response (1/2) plus = 37/80 ∧
    response (1/2) minus = 19/40 := by
  norm_num [response, plus, minus]

theorem witness_second_probe_gap :
    response (1/2) minus - response (1/2) plus = 1/80 := by
  norm_num [response, plus, minus]

theorem witness_difference_factorization (s : ℚ) :
    response s plus - response s minus =
      (1/6 : ℚ)*(s-1)^2*(s-4/5) := by
  dsimp [response, plus, minus]
  ring

/-- Zero total mass, zero first moment, and one vanished probe at t
force the difference polynomial to have the stated factorization. -/
theorem zeroes_imply_factor
    (a b c d t s : ℚ) (ht : t ≠ 1)
    (h_mass : a+b+c+d = 0)
    (h_mean : b+2*c+3*d = 0)
    (h_probe : a+b*t+c*t^2+d*t^3 = 0) :
    a+b*s+c*s^2+d*s^3 = d*(s-1)^2*(s-t) := by
  have ha : a = c + 2*d := by linarith [h_mass,h_mean]
  have hb : b = -2*c - 3*d := by linarith [h_mean]
  have ht_nonzero : (t-1)^2 ≠ 0 :=
    pow_ne_zero 2 (sub_ne_zero.mpr ht)
  have hfactor : (t-1)^2*(c+d*(t+2)) = 0 := by
    calc
      _ = a+b*t+c*t^2+d*t^3 := by rw [ha,hb]; ring
      _ = 0 := h_probe
  have hc_zero : c+d*(t+2) = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left ht_nonzero
  have hc : c = -d*(t+2) := by linarith [hc_zero]
  rw [ha,hb,hc]
  ring

/-- Two distinct nontrivial probes, plus mass and mean, determine all
four coefficients in the exact noiseless finite model. -/
theorem two_probes_zero
    (a b c d t s : ℚ) (ht : t ≠ 1)
    (hs : s ≠ 1) (hst : s ≠ t)
    (h_mass : a+b+c+d = 0)
    (h_mean : b+2*c+3*d = 0)
    (h_probe_t : a+b*t+c*t^2+d*t^3 = 0)
    (h_probe_s : a+b*s+c*s^2+d*s^3 = 0) :
    a=0 ∧ b=0 ∧ c=0 ∧ d=0 := by
  have hf := zeroes_imply_factor a b c d t s ht h_mass h_mean h_probe_t
  have hprod : d*(s-1)^2*(s-t) = 0 := by
    rw [← hf]
    exact h_probe_s
  have hnonzero : (s-1)^2*(s-t) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr hs))
      (sub_ne_zero.mpr hst)
  have hd : d=0 := by
    have hx : d*((s-1)^2*(s-t)) = 0 := by
      simpa only [mul_assoc] using hprod
    exact (mul_eq_zero.mp hx).resolve_right hnonzero
  have hzero := zeroes_imply_factor a b c d t 0 ht h_mass h_mean h_probe_t
  have ha : a=0 := by simpa [hd] using hzero
  have hc : c=0 := by linarith [h_mass,h_mean,ha,hd]
  have hb : b=0 := by linarith [h_mass,ha,hc,hd]
  exact ⟨ha,hb,hc,hd⟩

theorem two_probe_injective (p q : Profile) (t s : ℚ)
    (ht : t ≠ 1) (hs : s ≠ 1) (hst : s ≠ t)
    (hmass : mass p = mass q)
    (hmean : mean p = mean q)
    (ht_obs : response t p = response t q)
    (hs_obs : response s p = response s q) : p = q := by
  have h0 : (p.p0-q.p0)+(p.p1-q.p1)+(p.p2-q.p2)+(p.p3-q.p3) = 0 := by
    dsimp [mass] at hmass
    linarith
  have h1 : (p.p1-q.p1)+2*(p.p2-q.p2)+3*(p.p3-q.p3) = 0 := by
    dsimp [mean] at hmean
    linarith
  have h2 : (p.p0-q.p0)+(p.p1-q.p1)*t+
      (p.p2-q.p2)*t^2+(p.p3-q.p3)*t^3 = 0 := by
    dsimp [response] at ht_obs
    linear_combination ht_obs
  have h3 : (p.p0-q.p0)+(p.p1-q.p1)*s+
      (p.p2-q.p2)*s^2+(p.p3-q.p3)*s^3 = 0 := by
    dsimp [response] at hs_obs
    linear_combination hs_obs
  obtain ⟨hA,hB,hC,hD⟩ :=
    two_probes_zero (p.p0-q.p0) (p.p1-q.p1)
      (p.p2-q.p2) (p.p3-q.p3) t s ht hs hst h0 h1 h2 h3
  cases p with
  | mk p0 p1 p2 p3 =>
    cases q with
    | mk q0 q1 q2 q3 =>
      dsimp at hA hB hC hD
      have e0 : p0=q0 := by linarith [hA]
      have e1 : p1=q1 := by linarith [hB]
      have e2 : p2=q2 := by linarith [hC]
      have e3 : p3=q3 := by linarith [hD]
      subst q0
      subst q1
      subst q2
      subst q3
      rfl

end PADFourLayer
