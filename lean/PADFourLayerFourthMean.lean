import PADFourLayerFourProbe

/-!
# Fourth-probe mean constraint: exact certificates (additive)
The PR #101, #103, #106 original modules are not modified.
Four equal mass-only responses can be identical for strictly positive profiles
with different means. Wronskian factors and positivity certificates below
support an external Rolle argument for r=4/3; that analytic argument and
real-power calibration are NOT formalized here.
-/
namespace PADFourLayerFourthMean
open PADFourLayer

def massOnlyP : Profile :=
  ⟨155406813431861/3135446314560000,
    307250787839/10451487715200,
    5341857272874251/15677231572800000,
    379061002125331/653217982200000⟩
def massOnlyQ : Profile :=
  ⟨9757217468803/196456536000000,
    21675828291197/196456536000000,
    4/5, 1/25⟩

theorem massOnly_positive :
    0 < massOnlyP.p0 ∧ 0 < massOnlyP.p1 ∧
    0 < massOnlyP.p2 ∧ 0 < massOnlyP.p3 ∧
    0 < massOnlyQ.p0 ∧ 0 < massOnlyQ.p1 ∧
    0 < massOnlyQ.p2 ∧ 0 < massOnlyQ.p3 := by
  norm_num [massOnlyP, massOnlyQ]

theorem massOnly_masses :
    mass massOnlyP = 1 ∧ mass massOnlyQ = 1 := by
  norm_num [mass, massOnlyP, massOnlyQ]

theorem massOnly_four_equalities :
    response (1/64) massOnlyP = response (1/256) massOnlyQ ∧
    response (1/27) massOnlyP = response (1/81) massOnlyQ ∧
    response (1/8) massOnlyP = response (1/16) massOnlyQ ∧
    response (64/125) massOnlyP = response (256/625) massOnlyQ := by
  norm_num [response, massOnlyP, massOnlyQ]

theorem massOnly_means_differ :
    mean massOnlyP ≠ mean massOnlyQ := by
  norm_num [mean, massOnlyP, massOnlyQ]

theorem massOnly_distinct : massOnlyP ≠ massOnlyQ := by
  intro h
  have h0 := congrArg Profile.p3 h
  norm_num [massOnlyP, massOnlyQ] at h0

def A (t : ℚ) : ℚ :=
  5*t^5-4*t^4-4*t^3+16*t^2-2*t-2
def B (t : ℚ) : ℚ :=
  -t^2*(t^7+t^6+t^5-7*t^4-7*t^3+11*t^2-9*t-9)
def C (t : ℚ) : ℚ :=
  9*t^5*(t^2+t+1)*(t^6-3*t^3+3)
def E (t : ℚ) : ℚ :=
  40*t^11+79*t^10+76*t^9+110*t^8+260*t^7+
  605*t^6+672*t^5+474*t^4+24*t^3-138*t^2-120*t-30
def PB (t : ℚ) : ℚ :=
  20*t^10+35*t^9+20*t^8+50*t^7+200*t^6+455*t^5+
  380*t^4+80*t^3+200*t^2+144*t+36
def dA (t : ℚ) : ℚ :=
  25*t^4-16*t^3-12*t^2+32*t-2
def dB (t : ℚ) : ℚ :=
  -9*t^8-8*t^7-7*t^6+42*t^5+35*t^4-44*t^3+27*t^2+18*t
def dC (t : ℚ) : ℚ :=
  117*t^12+108*t^11+99*t^10-270*t^9-243*t^8-216*t^7+
  189*t^6+162*t^5+135*t^4

theorem A_right_certificate (t : ℚ) :
    A t =
      13*(1-t)^5+117*(2*t-1)*(1-t)^4+
      222*(2*t-1)^2*(1-t)^3+174*(2*t-1)^3*(1-t)^2+
      63*(2*t-1)^4*(1-t)+9*(2*t-1)^5 := by
  unfold A
  ring

theorem A_positive_right (t : ℚ) (hhalf : 1/2 ≤ t) (hone : t ≤ 1) :
    0 < A t := by
  rw [A_right_certificate]
  have hnonneg : 0 ≤ 2*t-1 := by linarith
  by_cases hlt : t < 1
  · have hpos : 0 < 1-t := by linarith
    positivity
  · have heq : t = 1 := by
      have hge : 1 ≤ t := le_of_not_gt hlt
      exact le_antisymm hone hge
    subst t
    norm_num

theorem B_positive_certificate (t : ℚ) :
    B t =
      9*t^2*(1-t)^7+72*t^3*(1-t)^6+
      232*t^4*(1-t)^5+402*t^5*(1-t)^4+
      420*t^6*(1-t)^3+276*t^7*(1-t)^2+
      108*t^8*(1-t)+18*t^9 := by
  unfold B
  ring

theorem B_positive (t : ℚ) (h0 : 0 < t) (h1 : t < 1) : 0 < B t := by
  rw [B_positive_certificate]
  have hdiff : 0 < 1-t := by linarith
  positivity

theorem C_positive (t : ℚ) (h0 : 0 < t) : 0 < C t := by
  have hh : 0 < t^6-3*t^3+3 := by
    nlinarith [sq_nonneg (t^3-(3/2 : ℚ))]
  unfold C
  positivity

theorem E_left_certificate (t : ℚ) :
    -(2048 : ℚ)*E t =
      61440*(1-2*t)^11+
      798720*(2*t)*(1-2*t)^10+
      4678656*(2*t)^2*(1-2*t)^9+
      16296960*(2*t)^3*(1-2*t)^8+
      37454592*(2*t)^4*(1-2*t)^7+
      59485440*(2*t)^5*(1-2*t)^6+
      66358112*(2*t)^6*(1-2*t)^5+
      51682976*(2*t)^7*(1-2*t)^4+
      27279440*(2*t)^8*(1-2*t)^3+
      9139648*(2*t)^9*(1-2*t)^2+
      1691794*(2*t)^10*(1-2*t)+
      120250*(2*t)^11 := by
  unfold E
  ring

theorem E_negative_left (t : ℚ) (h0 : 0 < t) (hhalf : t < 1/2) :
    E t < 0 := by
  have hx : 0 < 2*t := by linarith
  have hy : 0 < 1-2*t := by linarith
  have hsum :
      0 < (61440 : ℚ)*(1-2*t)^11+
      798720*(2*t)*(1-2*t)^10+
      4678656*(2*t)^2*(1-2*t)^9+
      16296960*(2*t)^3*(1-2*t)^8+
      37454592*(2*t)^4*(1-2*t)^7+
      59485440*(2*t)^5*(1-2*t)^6+
      66358112*(2*t)^6*(1-2*t)^5+
      51682976*(2*t)^7*(1-2*t)^4+
      27279440*(2*t)^8*(1-2*t)^3+
      9139648*(2*t)^9*(1-2*t)^2+
      1691794*(2*t)^10*(1-2*t)+
      120250*(2*t)^11 := by
    positivity
  have hid := E_left_certificate t
  linarith

theorem AB_wronskian (t : ℚ) :
    A t*dB t-dA t*B t = -t*(t-1)^2*PB t := by
  unfold A B PB dA dB
  ring

theorem AC_wronskian (t : ℚ) :
    A t*dC t-dA t*C t = 9*t^4*(t-1)^2*E t := by
  unfold A C E dA dC
  ring

theorem AB_wronskian_negative (t : ℚ) (h0 : 0 < t) (h1 : t < 1) :
    A t*dB t-dA t*B t < 0 := by
  rw [AB_wronskian]
  have hp : 0 < PB t := by
    unfold PB
    positivity
  have hs : 0 < (t-1)^2 := by
    have hz : 0 < (1-t)^2 := pow_pos (by linarith) 2
    nlinarith
  have hh : 0 < t*(t-1)^2*PB t := mul_pos (mul_pos h0 hs) hp
  linarith

theorem AC_wronskian_negative (t : ℚ) (h0 : 0 < t) (hhalf : t < 1/2) :
    A t*dC t-dA t*C t < 0 := by
  rw [AC_wronskian]
  have he := E_negative_left t h0 hhalf
  have hs : 0 < (t-1)^2 := by
    have hz : 0 < (1-t)^2 := pow_pos (by linarith) 2
    nlinarith
  have hfactor : 0 < (9 : ℚ)*t^4*(t-1)^2 := by positivity
  nlinarith [mul_neg_of_pos_of_neg hfactor he]

end PADFourLayerFourthMean
