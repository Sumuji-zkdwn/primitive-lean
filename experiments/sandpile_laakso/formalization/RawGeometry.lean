import ObservedQuotient
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Tactic

/-! Exact unweighted horizontal distance as a shortest sweep across the gates.
A path must visit a gate for each differing digit. On an interval [l,u] the
shorter of the two sweep orders has length 2(u-l)-|t-t'|. The full interval is
always feasible. Applying this at finite depth and using nested compact
subsets of [-1,1]^2 gives the same infimum for the infinite-label quotient. -/
namespace ObservedSandpile.Raw
open ObservedSandpile MeasureTheory Set
noncomputable section

abbrev Point (e : H ≃ H) :=
  Quot (liftRel (C := Phase) (gate (fun t k => ternary (e t) k)))
abbrev Rep := (H × Bits) × Phase

def height (e : H ≃ H) : Point e → H :=
  Quot.lift (fun x : Rep => x.1.1) (by
    rintro x y ⟨⟨k,_,he⟩,_⟩
    exact (congrArg Prod.fst he).symm)

theorem out_height (e : H ≃ H) (x : Point e) : x.out.1.1 = height e x :=
  congrArg (height e) x.out_eq

def admissible (e : H ≃ H) (x y : Rep) (l u : H) : Prop :=
  l ≤ x.1.1 ∧ l ≤ y.1.1 ∧ x.1.1 ≤ u ∧ y.1.1 ≤ u ∧
  ∀ k, x.1.2 k ≠ y.1.2 k → ∃ z : H, l ≤ z ∧ z ≤ u ∧ ternary (e z) k

def costs (e : H ≃ H) (x y : Rep) : Set ℝ :=
  {w | ∃ l u : H, admissible e x y l u ∧
       w = 2*(u.1-l.1) - |x.1.1.1-y.1.1.1|}

private theorem gate_exists (k : ℕ) : ∃ z : H, ternary z k := by
  have hM : (1:ℕ) < 3^(k+1) := Nat.one_lt_pow (by omega) (by decide)
  have h : (1:ℝ) < 3^(k+1) := by exact_mod_cast hM
  let v : ℝ := 2/(3^(k+1):ℝ)-1
  have hv : v ∈ Icc (-1:ℝ) 1 := by
    constructor
    · dsimp [v]; linarith [show (0:ℝ) ≤ 2/3^(k+1) by positivity]
    · dsimp [v]; have := (div_le_iff₀ (by positivity : (0:ℝ)<3^(k+1))).2
          (show (2:ℝ) ≤ 2*3^(k+1) by linarith)
      linarith
  refine ⟨⟨v,hv⟩,1,by decide,hM,by decide,?_⟩
  simp [v]

private theorem range_full (e : H ≃ H) (x y : Rep) :
    4 - |x.1.1.1 - y.1.1.1| ∈ costs e x y := by
  let l : H := ⟨-1,by constructor <;> norm_num⟩
  let u : H := ⟨1,by constructor <;> norm_num⟩
  refine ⟨l,u,⟨x.1.1.2.1,y.1.1.2.1,x.1.1.2.2,y.1.1.2.2,?_⟩,?_⟩
  · intro k _
    obtain ⟨z,hz⟩ := gate_exists k
    exact ⟨e.symm z,(e.symm z).2.1,(e.symm z).2.2,by simpa using hz⟩
  · dsimp [u,l]; ring

private theorem lower_cost (e : H ≃ H) (x y : Rep) {w : ℝ} (hw : w ∈ costs e x y) :
    |x.1.1.1-y.1.1.1| ≤ w := by
  obtain ⟨l,u,⟨hlx,hly,hxu,hyu,_⟩,rfl⟩ := hw
  change l.1 ≤ x.1.1.1 at hlx
  change l.1 ≤ y.1.1.1 at hly
  change x.1.1.1 ≤ u.1 at hxu
  change y.1.1.1 ≤ u.1 at hyu
  have h : |x.1.1.1-y.1.1.1| ≤ u.1-l.1 := abs_le.mpr ⟨by linarith,by linarith⟩
  linarith

def distance (e : H ≃ H) (x y : Point e) : ℝ :=
  sInf (costs e x.out y.out) + dist x.out.2 y.out.2

theorem height_control (e : H ≃ H) (x y : Point e) :
    |(height e x).1-(height e y).1| ≤ distance e x y := by
  rw [← out_height e x, ← out_height e y]
  exact (le_csInf ⟨_,range_full e x.out y.out⟩ (fun _ h => lower_cost _ _ _ h)).trans
    (le_add_of_nonneg_right dist_nonneg)

theorem diameter_bound (e : H ≃ H) (x y : Point e) : distance e x y < 5 := by
  have hb : BddBelow (costs e x.out y.out) := ⟨_,fun _ h => lower_cost _ _ _ h⟩
  have hi := csInf_le hb (range_full e x.out y.out)
  have hc : dist x.out.2 y.out.2 ≤ (1:ℝ)/2 := by
    rw [dist_eq_norm]
    simpa using (AddCircle.norm_le_half_period 1 (x := x.out.2-y.out.2) one_ne_zero)
  unfold distance
  linarith [abs_nonneg (x.out.1.1.1-y.out.1.1.1)]

def data {Ω : Type*} [MeasurableSpace Ω] (e : H ≃ H) (μ : Measure Ω) (read : Ω → Point e) :
    Observation Ω (Point e) where
  law := μ
  readout := read
  distance := distance e
  borelTest g := Measurable (g ∘ read)

#print axioms height_control
#print axioms diameter_bound
end
end ObservedSandpile.Raw
