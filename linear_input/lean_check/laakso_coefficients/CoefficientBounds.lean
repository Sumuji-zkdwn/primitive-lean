import PinnedLaakso
import Mathlib.Tactic.LinearCombination

/-! Local parameter extension of PR #154. The original declarations are imported
from the pinned source files by replay_lean.py. All states here are real. -/

noncomputable section
namespace LaaksoCoefficientBounds

open LinearInputLaaksoFiniteGraph LinearInputLaaksoSigned LinearInputLaaksoSignedEnergy
open LinearInputLaaksoSignedGauge LinearInputLaaksoSignedMinimum

def potential (l : ℝ) (p : ℝ × ℝ) : ℝ :=
  l / 4 * (p.1 ^ 2 - 1 / l) ^ 2 + (p.2 - Real.sqrt 2 * p.1) ^ 2 / 2

def total (l k : ℝ) (τ : Twist) (q : State) : ℝ :=
  (∑ v : Fin 6, potential l (q v)) + k * ∑ e : Fin 6, edgeEnergy τ q e

def onsiteExcess (l : ℝ) (p : ℝ × ℝ) : ℝ :=
  l * p.1 ^ 4 / 4 - p.1 ^ 2 / 2 + (p.2 - Real.sqrt 2 * p.1) ^ 2 / 2

theorem potential_split {l : ℝ} (hl : 0 < l) (p : ℝ × ℝ) :
    potential l p = 1 / (4*l) + onsiteExcess l p := by
  unfold potential onsiteExcess
  field_simp [hl.ne']
  ring

def edgeShare (p c : ℝ × ℝ) : ℝ :=
  ((p.1 - c.1)^2 + (p.2 - c.2)^2 + c.1^2 + c.2^2) / 2

def block (l k : ℝ) (p c : ℝ × ℝ) : ℝ :=
  onsiteExcess l p + onsiteExcess l c / 2 + k * edgeShare p c

theorem block_correction (l k : ℝ) (p c : ℝ × ℝ) :
    block l k p c = leafExcess p c + (l-1) * (p.1^4 / 4 + c.1^4 / 8) +
      (k-1) * edgeShare p c := by
  unfold block onsiteExcess edgeShare leafExcess
  ring_nf
  norm_num [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  ring

def fourBlocks (f : (ℝ × ℝ) → (ℝ × ℝ) → ℝ) (q : State) : ℝ :=
  f (q 0) (q 4) + f (q 1) (q 4) + f (q 2) (q 5) + f (q 3) (q 5)

theorem decomposition {l : ℝ} (hl : 0 < l) (k : ℝ) (q : State) :
    total l k flipped q = 3/(2*l) + fourBlocks (block l k) q := by
  simp only [total, sum_six, potential_split hl, fourBlocks, block]
  simp [edgeEnergy, flipped, sign, firstSource, firstTarget, edgeShare,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem switching (l k : ℝ) (g : Spin) (τ : Twist) (q : State) :
    total l k (switchTwist g τ) (switchState g q) = total l k τ q := by
  have h (v : Fin 6) : potential l (switchState g q v) = potential l (q v) := by
    cases hv : g v <;> simp [switchState, potential, hv]
    ring
  simp only [total, h, edgeEnergy_switch]

theorem total_origin {l : ℝ} (hl : 0 < l) (k : ℝ) (τ : Twist) :
    total l k τ (fun _ => (0,0)) = 3/(2*l) := by
  simp [total, potential_split hl, onsiteExcess, edgeEnergy]
  ring

/-- Center-to-leaf ratio of the lowest signed Laplacian mode. -/
def leafRatio : ℝ := (Real.sqrt 17 - 3) / 2
def lowestEigenvalue : ℝ := 1 - leafRatio

theorem ratio_pos : 0 < leafRatio := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 17)
  have h0 := Real.sqrt_nonneg (17:ℝ)
  unfold leafRatio
  nlinarith

theorem ratio_relation : leafRatio ^ 2 + 3*leafRatio = 2 := by
  unfold leafRatio
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 17)]

theorem eigenvalue_pos : 0 < lowestEigenvalue := by
  unfold lowestEigenvalue leafRatio
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 17)]

def critical : ℝ := (Real.sqrt 2 - 1) / lowestEigenvalue

/-- A one-coordinate identity for one leaf and half of its adjacent center. -/
theorem edge_square (v w : ℝ) :
    (v-w)^2 + w^2 = lowestEigenvalue * (v^2 + w^2/2) +
      (leafRatio*v-w)^2 / leafRatio := by
  unfold lowestEigenvalue
  field_simp [ratio_pos.ne']
  linear_combination (w^2) * ratio_relation

def mass (p c : ℝ × ℝ) : ℝ := p.1^2 + p.2^2 + (c.1^2 + c.2^2)/2
def modeError (p c : ℝ × ℝ) : ℝ :=
  ((leafRatio*p.1-c.1)^2 + (leafRatio*p.2-c.2)^2) / leafRatio

theorem split_edge (p c : ℝ × ℝ) :
    edgeShare p c = (lowestEigenvalue * mass p c + modeError p c)/2 := by
  unfold edgeShare mass modeError
  linear_combination (edge_square p.1 c.1 + edge_square p.2 c.2) / 2

theorem split_onsite (l : ℝ) (p : ℝ × ℝ) :
    onsiteExcess l p = l*p.1^4/4 + Real.sqrt 2 / 2 * (p.1-p.2)^2 +
      (1-Real.sqrt 2)/2 * (p.1^2+p.2^2) := by
  unfold onsiteExcess
  linear_combination (p.1^2/2) * Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)

def wellSquares (p c : ℝ × ℝ) : ℝ := p.1^4/4 + c.1^4/8
def componentSquares (p c : ℝ × ℝ) : ℝ := (p.1-p.2)^2 + (c.1-c.2)^2/2

theorem block_squares (l k : ℝ) (p c : ℝ × ℝ) :
    block l k p c = l * wellSquares p c + Real.sqrt 2/2 * componentSquares p c +
      (1-Real.sqrt 2 + k*lowestEigenvalue)/2 * mass p c + k/2 * modeError p c := by
  rw [block, split_onsite, split_onsite, split_edge]
  unfold wellSquares componentSquares mass
  ring

theorem block_bound (l : ℝ) {k : ℝ} (hk : 0 ≤ k) (hc : critical ≤ k)
    (p c : ℝ × ℝ) :
    l * wellSquares p c + Real.sqrt 2/2 * componentSquares p c ≤ block l k p c := by
  have hc' := (div_le_iff₀ eigenvalue_pos).mp hc
  have hm : 0 ≤ (1-Real.sqrt 2+k*lowestEigenvalue)/2 := by linarith
  have hn : 0 ≤ mass p c := by unfold mass; positivity
  have hd := ratio_pos
  have he : 0 ≤ modeError p c := by unfold modeError; positivity
  rw [block_squares]
  linarith [mul_nonneg hm hn, mul_nonneg (show 0 ≤ k/2 by positivity) he]

theorem block_nonneg {l k : ℝ} (hl : 0 < l) (hk : 0 ≤ k) (hc : critical ≤ k)
    (p c : ℝ × ℝ) : 0 ≤ block l k p c := by
  apply le_trans _ (block_bound l hk hc p c)
  unfold wellSquares componentSquares
  positivity

theorem block_zero {l k : ℝ} (hl : 0 < l) (hk : 0 ≤ k) (hc : critical ≤ k)
    {p c : ℝ × ℝ} (h : block l k p c = 0) : p = (0,0) ∧ c = (0,0) := by
  have b := block_bound l hk hc p c
  rw [h] at b
  have hw : 0 ≤ wellSquares p c := by unfold wellSquares; positivity
  have hd : 0 ≤ componentSquares p c := by unfold componentSquares; positivity
  have hr : 0 < Real.sqrt 2 / 2 := by positivity
  have w : wellSquares p c = 0 := by
    by_contra! hp
    have hp' : 0 < wellSquares p c := lt_of_le_of_ne hw (Ne.symm hp)
    linarith [mul_pos hl hp', mul_nonneg hr.le hd]
  have d : componentSquares p c = 0 := by
    by_contra! hp
    have hp' : 0 < componentSquares p c := lt_of_le_of_ne hd (Ne.symm hp)
    linarith [mul_pos hr hp', mul_nonneg hl.le hw]
  unfold wellSquares at w
  unfold componentSquares at d
  have hx : p.1^4 = 0 := by linarith [show 0 ≤ p.1^4 by positivity, show 0 ≤ c.1^4 by positivity]
  have ha : c.1^4 = 0 := by linarith [show 0 ≤ p.1^4 by positivity, show 0 ≤ c.1^4 by positivity]
  have he : (p.1-p.2)^2 = 0 := by linarith [sq_nonneg (p.1-p.2), sq_nonneg (c.1-c.2)]
  have hf : (c.1-c.2)^2 = 0 := by linarith [sq_nonneg (p.1-p.2), sq_nonneg (c.1-c.2)]
  have px : p.1 = 0 := by simpa using hx
  have cx : c.1 = 0 := by simpa using ha
  have py : p.2 = 0 := by simpa [px] using he
  have cy : c.2 = 0 := by simpa [cx] using hf
  exact ⟨Prod.ext px py, Prod.ext cx cy⟩

private theorem normalize_odd {τ : Twist} (hodd : middleParity τ = true) :
    switchTwist (treeGauge τ) τ = flipped := by
  rw [tree_normal_form, hodd]
  rfl

theorem odd_bound {l k : ℝ} (hl : 0 < l) (hk : 0 ≤ k) (hc : critical ≤ k)
    {τ : Twist} (hodd : middleParity τ = true) (q : State) :
    3/(2*l) ≤ total l k τ q := by
  rw [← switching l k (treeGauge τ) τ q, normalize_odd hodd,
    decomposition hl, fourBlocks]
  let s := switchState (treeGauge τ) q
  change 3/(2*l) ≤ 3/(2*l) + (block l k (s 0) (s 4) + block l k (s 1) (s 4) +
      block l k (s 2) (s 5) + block l k (s 3) (s 5))
  have b := block_nonneg hl hk hc
  linarith [b (s 0) (s 4), b (s 1) (s 4), b (s 2) (s 5), b (s 3) (s 5)]

theorem odd_eq_iff {l k : ℝ} (hl : 0 < l) (hk : 0 ≤ k) (hc : critical ≤ k)
    {τ : Twist} (hodd : middleParity τ = true) (q : State) :
    total l k τ q = 3/(2*l) ↔ q = fun _ => (0,0) := by
  constructor
  · intro h
    rw [← switching l k (treeGauge τ) τ q, normalize_odd hodd,
      decomposition hl, fourBlocks] at h
    let s := switchState (treeGauge τ) q
    have hz : block l k (s 0) (s 4) + block l k (s 1) (s 4) +
        block l k (s 2) (s 5) + block l k (s 3) (s 5) = 0 := by
      change 3/(2*l) + _ = 3/(2*l) at h
      exact add_left_cancel (h.trans (add_zero _).symm)
    have hn := block_nonneg hl hk hc
    rw [add_eq_zero_iff_of_nonneg
          (add_nonneg (add_nonneg (hn (s 0) (s 4)) (hn (s 1) (s 4))) (hn (s 2) (s 5))) (hn (s 3) (s 5)),
        add_eq_zero_iff_of_nonneg (add_nonneg (hn (s 0) (s 4)) (hn (s 1) (s 4))) (hn (s 2) (s 5)),
        add_eq_zero_iff_of_nonneg (hn (s 0) (s 4)) (hn (s 1) (s 4))] at hz
    obtain ⟨⟨⟨h0,h1⟩,h2⟩,h3⟩ := hz
    obtain ⟨z0,z4⟩ := block_zero hl hk hc h0
    obtain ⟨z1,_⟩ := block_zero hl hk hc h1
    obtain ⟨z2,z5⟩ := block_zero hl hk hc h2
    obtain ⟨z3,_⟩ := block_zero hl hk hc h3
    apply (switchState_eq_zero_iff _ _).mp
    change s = _
    funext v
    fin_cases v <;> assumption
  · rintro rfl
    exact total_origin hl k τ

def trial (t : ℝ) : State :=
  ![(t,t), (t,t), (t,t), (t,t), (leafRatio*t,leafRatio*t), (leafRatio*t,leafRatio*t)]

theorem trial_energy {l : ℝ} (hl : 0 < l) (k t : ℝ) :
    total l k flipped (trial t) = 3/(2*l) + l*(1+leafRatio^4/2)*t^4 +
      (1-Real.sqrt 2+k*lowestEigenvalue)*(4+2*leafRatio^2)*t^2 := by
  rw [decomposition hl]
  simp [fourBlocks, trial, block_squares, wellSquares, componentSquares, mass, modeError]
  ring

theorem quartic_dips {a b : ℝ} (ha : 0 < a) (hb : b < 0) :
    ∃ t : ℝ, a*t^4 + b*t^2 < 0 := by
  let t := Real.sqrt (-b/(2*a))
  have h : 0 < -b/(2*a) := div_pos (neg_pos.mpr hb) (by positivity)
  have ht : t^2 = -b/(2*a) := Real.sq_sqrt h.le
  refine ⟨t, ?_⟩
  rw [show t^4 = (t^2)^2 by ring, ht]
  calc
    _ = -(b^2)/(4*a) := by field_simp [ha.ne']; ring
    _ < 0 := div_neg_of_neg_of_pos (neg_lt_zero.mpr (sq_pos_of_ne_zero hb.ne)) (by positivity)

theorem odd_below_critical {l k : ℝ} (hl : 0 < l) (hc : k < critical)
    {τ : Twist} (hodd : middleParity τ = true) : ∃ q, total l k τ q < 3/(2*l) := by
  have hc' := (lt_div_iff₀ eigenvalue_pos).mp hc
  have ha : 0 < l*(1+leafRatio^4/2) := by positivity
  have hb : (1-Real.sqrt 2+k*lowestEigenvalue)*(4+2*leafRatio^2) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) (by positivity)
  obtain ⟨t,ht⟩ := quartic_dips ha hb
  let g := treeGauge τ
  have hn : switchTwist g τ = flipped := normalize_odd hodd
  have back : switchTwist g flipped = τ := by rw [← hn, switch_involutive]
  refine ⟨switchState g (trial t), ?_⟩
  have h := switching l k g flipped (trial t)
  rw [back, trial_energy hl] at h
  linarith

theorem odd_origin_minimal_iff {l k : ℝ} (hl : 0 < l) (hk : 0 ≤ k)
    {τ : Twist} (hodd : middleParity τ = true) :
    (∀ q, 3/(2*l) ≤ total l k τ q) ↔ critical ≤ k := by
  constructor
  · intro h
    by_contra! hc
    obtain ⟨q,hq⟩ := odd_below_critical hl hc hodd
    exact (not_lt_of_ge (h q)) hq
  · exact fun hc q => odd_bound hl hk hc hodd q

def rescale (r : ℝ) (q : State) : State := fun v => (r*(q v).1,r*(q v).2)

theorem potential_rescale {l : ℝ} (hl : 0 < l) (p : ℝ × ℝ) :
    potential 1 (Real.sqrt l*p.1,Real.sqrt l*p.2) = l*potential l p := by
  have h₁ : (Real.sqrt l*p.1)^2-1 = l*(p.1^2-1/l) := by
    rw [mul_pow, Real.sq_sqrt hl.le]
    field_simp [hl.ne']
  have h₂ : (Real.sqrt l*p.2-Real.sqrt 2*(Real.sqrt l*p.1))^2 =
      l*(p.2-Real.sqrt 2*p.1)^2 := by
    rw [show Real.sqrt l*p.2-Real.sqrt 2*(Real.sqrt l*p.1) =
      Real.sqrt l*(p.2-Real.sqrt 2*p.1) by ring, mul_pow, Real.sq_sqrt hl.le]
  simp only [potential, div_one]
  rw [h₁,h₂]
  ring

theorem edge_rescale (r : ℝ) (τ : Twist) (q : State) (e : Fin 6) :
    edgeEnergy τ (rescale r q) e = r^2*edgeEnergy τ q e := by
  unfold edgeEnergy rescale
  ring

theorem scale_identity {l : ℝ} (hl : 0 < l) (k : ℝ) (τ : Twist) (q : State) :
    total 1 k τ (rescale (Real.sqrt l) q) = l*total l k τ q := by
  unfold total
  simp only [edge_rescale, Real.sq_sqrt hl.le, rescale, potential_rescale hl, ← Finset.mul_sum]
  ring

theorem weighted_comparison (k : ℝ) (τ : Twist) (q : State) :
    min 1 k * energy τ q ≤ total 1 k τ q := by
  have hv := Finset.sum_nonneg (s := Finset.univ) (fun v _ => localPotential_nonneg (q v))
  have he := Finset.sum_nonneg (s := Finset.univ) (fun e _ => edgeEnergy_nonneg τ q e)
  have hp (p : ℝ × ℝ) : potential 1 p = localPotential p := by
    unfold potential localPotential
    norm_num
    ring
  simp only [total, energy, hp, mul_add]
  exact add_le_add (by simpa using mul_le_mul_of_nonneg_right (min_le_left (1:ℝ) k) hv)
    (mul_le_mul_of_nonneg_right (min_le_right (1:ℝ) k) he)

theorem odd_positive_bound {l k : ℝ} (hl : 0 < l) (hk : 0 ≤ k) {τ : Twist}
    (hodd : middleParity τ = true) (q : State) :
    3*min 1 k/(2*l) ≤ total l k τ q := by
  have h₁ := odd_minimum hodd (rescale (Real.sqrt l) q)
  have h₂ := weighted_comparison k τ (rescale (Real.sqrt l) q)
  rw [scale_identity hl] at h₂
  have hm : 0 ≤ min 1 k := le_min (by norm_num) hk
  have bound := (mul_le_mul_of_nonneg_left h₁ hm).trans h₂
  apply (div_le_iff₀ (show 0 < 2*l by positivity)).2
  linarith only [bound]

theorem potential_nonnegative {l : ℝ} (hl : 0 < l) (p : ℝ × ℝ) :
    0 ≤ potential l p := by unfold potential; positivity

theorem potential_zero {l : ℝ} (hl : 0 < l) (p : ℝ × ℝ) :
    potential l p = 0 ↔ p.1^2 = 1/l ∧ p.2 = Real.sqrt 2*p.1 := by
  unfold potential
  rw [add_eq_zero_iff_of_nonneg (by positivity) (by positivity)]
  simp [mul_eq_zero, div_eq_zero_iff, hl.ne', sub_eq_zero]

theorem all_terms_zero {l k : ℝ} (hl : 0 < l) (hk : 0 < k) (τ : Twist) (q : State) :
    total l k τ q = 0 ↔ (∀ v, potential l (q v) = 0) ∧ ∀ e, edgeEnergy τ q e = 0 := by
  have hv := Finset.sum_nonneg (s := Finset.univ) (fun v _ => potential_nonnegative hl (q v))
  have he := Finset.sum_nonneg (s := Finset.univ) (fun e _ => edgeEnergy_nonneg τ q e)
  rw [total, add_eq_zero_iff_of_nonneg hv (mul_nonneg hk.le he)]
  simp [mul_eq_zero, hk.ne', Finset.sum_eq_zero_iff_of_nonneg (fun v _ => potential_nonnegative hl (q v)),
    Finset.sum_eq_zero_iff_of_nonneg (fun e _ => edgeEnergy_nonneg τ q e)]

theorem untwisted_edge_zero (q : State) (e : Fin 6) :
    edgeEnergy untwisted q e = 0 ↔ q (firstSource e) = q (firstTarget e) := by
  have hx := sq_nonneg ((q (firstSource e)).1 - (q (firstTarget e)).1)
  have hy := sq_nonneg ((q (firstSource e)).2 - (q (firstTarget e)).2)
  simp [edgeEnergy, sign_untwisted, Prod.ext_iff, div_eq_zero_iff,
    add_eq_zero_iff_of_nonneg hx hy, sub_eq_zero]

theorem untwisted_zero {l k : ℝ} (hl : 0 < l) (hk : 0 < k) (q : State) :
    total l k untwisted q = 0 ↔ ∃ a : ℝ, a^2 = 1/l ∧ q = fun _ => (a,Real.sqrt 2*a) := by
  rw [all_terms_zero hl hk]
  constructor
  · rintro ⟨hp,he⟩
    have edge (e : Fin 6) := (untwisted_edge_zero q e).mp (he e)
    have e0 : q 0 = q 4 := edge 0
    have e1 : q 1 = q 4 := edge 1
    have e2 : q 4 = q 5 := edge 2
    have e4 : q 5 = q 2 := edge 4
    have e5 : q 5 = q 3 := edge 5
    have same (v : Fin 6) : q v = q 4 := by
      fin_cases v
      exacts [e0,e1,e4.symm.trans e2.symm,e5.symm.trans e2.symm,rfl,e2.symm]
    have h := (potential_zero hl (q 4)).mp (hp 4)
    refine ⟨(q 4).1, h.1, ?_⟩
    funext v
    rw [same v]
    exact Prod.ext rfl h.2
  · rintro ⟨a,ha,rfl⟩
    exact ⟨fun _ => (potential_zero hl _).mpr ⟨ha,rfl⟩,
      fun e => (untwisted_edge_zero _ e).mpr rfl⟩

theorem even_eq_iff {l k : ℝ} (hl : 0 < l) (hk : 0 < k) {τ : Twist}
    (heven : middleParity τ = false) (q : State) :
    total l k τ q = 0 ↔ ∃ a : ℝ, a^2 = 1/l ∧
      switchState (treeGauge τ) q = fun _ => (a,Real.sqrt 2*a) := by
  rw [← switching l k (treeGauge τ) τ q, tree_normal_form, heven]
  exact untwisted_zero hl hk _

theorem even_least {l k : ℝ} (hl : 0 < l) (hk : 0 < k) {τ : Twist}
    (heven : middleParity τ = false) : IsLeast (Set.range (total l k τ)) 0 := by
  let a := Real.sqrt (1/l)
  let q : State := fun _ => (a,Real.sqrt 2*a)
  have hq : total l k untwisted q = 0 := (untwisted_zero hl hk q).mpr
    ⟨a, Real.sq_sqrt (by positivity), rfl⟩
  let g := treeGauge τ
  have hn : switchTwist g τ = untwisted := by rw [tree_normal_form, heven]; rfl
  have back : switchTwist g untwisted = τ := by rw [← hn, switch_involutive]
  have h := switching l k g untwisted q
  rw [back, hq] at h
  refine ⟨⟨switchState g q,h⟩, ?_⟩
  rintro _ ⟨p,rfl⟩
  exact add_nonneg (Finset.sum_nonneg fun v _ => potential_nonnegative hl (p v))
    (mul_nonneg hk.le (Finset.sum_nonneg fun e _ => edgeEnergy_nonneg τ p e))

theorem odd_least {l k : ℝ} (hl : 0 < l) (hk : 0 ≤ k) (hc : critical ≤ k)
    {τ : Twist} (hodd : middleParity τ = true) :
    IsLeast (Set.range (total l k τ)) (3/(2*l)) := by
  refine ⟨⟨_,total_origin hl k τ⟩, ?_⟩
  rintro _ ⟨q,rfl⟩
  exact odd_bound hl hk hc hodd q

theorem weak_rational_witness : total 1 (1/8) flipped constantWell = 3/4 := by
  simp [total, sum_six, potential, constantWell, edgeEnergy, flipped, sign]
  ring_nf
  norm_num [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

#print axioms block_correction
#print axioms decomposition
#print axioms scale_identity
#print axioms even_eq_iff
#print axioms even_least
#print axioms odd_least
#print axioms odd_origin_minimal_iff
#print axioms odd_eq_iff
#print axioms odd_positive_bound
#print axioms weak_rational_witness

end LaaksoCoefficientBounds
end
