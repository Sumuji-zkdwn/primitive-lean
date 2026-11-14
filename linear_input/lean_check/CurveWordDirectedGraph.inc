/-!
The minimum-cycle-mean result for a finite directed multigraph whose outgoing
edge type may depend on the vertex. A policy letter chooses one actual edge
at each vertex. Encoding and decoding preserve every path, length, terminal
vertex and cost; this adds no artificial transitions or padding loops.
-/

noncomputable section
namespace LinearInputCurveWordDirectedGraph

open LinearInputCurveWordFiniteState LinearInputCurveWordGraphLimit

variable {Q : Type*} (Out : Q → Type*) (target : ∀ q, Out q → Q)

inductive Walk : Q → Type _
  | nil (q : Q) : Walk q
  | cons {q : Q} (e : Out q) (tail : Walk (target q e)) : Walk q

def Walk.length {q : Q} : Walk Out target q → ℕ
  | .nil _ => 0
  | .cons _ p => p.length + 1

def Walk.finish {q : Q} : Walk Out target q → Q
  | .nil q => q
  | .cons _ p => p.finish

def Walk.cost (c : ∀ q, Out q → ℝ) {q : Q} : Walk Out target q → ℝ
  | .nil _ => 0
  | .cons e p => c q e + Walk.cost c p

abbrev Policy := ∀ q, Out q

def policyNext (q : Q) (p : Policy Out) : Q := target q (p q)

def policyCost (c : ∀ q, Out q → ℝ) (q : Q) (p : Policy Out) : ℝ := c q (p q)

def decode (q : Q) : List (Policy Out) → Walk Out target q
  | [] => .nil q
  | p :: w => .cons (p q) (decode (target q (p q)) w)

theorem decode_length (q : Q) (w : List (Policy Out)) :
    (decode Out target q w).length = w.length := by
  induction w generalizing q with
  | nil => rfl
  | cons p w ih => simp only [decode, Walk.length, List.length_cons, ih]

theorem decode_finish (q : Q) (w : List (Policy Out)) :
    (decode Out target q w).finish = terminal (policyNext Out target) q w := by
  induction w generalizing q with
  | nil => rfl
  | cons p w ih => exact ih _

theorem decode_cost (c : ∀ q, Out q → ℝ) (q : Q) (w : List (Policy Out)) :
    Walk.cost Out target c (decode Out target q w) = wordCost (policyNext Out target) (policyCost Out c) q w := by
  induction w generalizing q with
  | nil => rfl
  | cons p w ih =>
    simpa only [decode, Walk.cost, wordCost, policyCost, policyNext] using
      (congrArg (fun x => c q (p q) + x) (ih (target q (p q))))

variable [DecidableEq Q] [∀ q, Nonempty (Out q)]

def edgePolicy (q : Q) (e : Out q) : Policy Out :=
  Function.update (fun r => Classical.choice (inferInstance : Nonempty (Out r))) q e

theorem edgePolicy_at (q : Q) (e : Out q) : edgePolicy Out q e q = e := by
  simp [edgePolicy]

def encode {q : Q} : Walk Out target q → List (Policy Out)
  | .nil _ => []
  | .cons e p => edgePolicy Out q e :: encode p

theorem encode_length {q : Q} (p : Walk Out target q) :
    (encode Out target p).length = p.length := by
  induction p with
  | nil => rfl
  | cons e p ih => simp only [encode, List.length_cons, Walk.length, ih]

theorem encode_finish {q : Q} (p : Walk Out target q) :
    terminal (policyNext Out target) q (encode Out target p) = p.finish := by
  induction p with
  | nil => rfl
  | cons e p ih => simpa only [encode, terminal, policyNext, edgePolicy_at, Walk.finish] using ih

theorem encode_cost (c : ∀ q, Out q → ℝ) {q : Q} (p : Walk Out target q) :
    wordCost (policyNext Out target) (policyCost Out c) q (encode Out target p) = Walk.cost Out target c p := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    simp only [encode, wordCost, policyNext, policyCost, edgePolicy_at, Walk.cost, ih]

variable [Fintype Q] [Nonempty Q] [∀ q, Fintype (Out q)]

def minimumMean (c : ∀ q, Out q → ℝ) : ℝ := by
  classical
  exact cycleMean (policyNext Out target) (policyCost Out c)

def optimum (c : ∀ q, Out q → ℝ) (q : Q) (n : ℕ) : ℝ := by
  classical
  exact bellman (policyNext Out target) (policyCost Out c) n q

omit [Nonempty Q] in
/-- A fixed-length optimum is an optimum over all actual walks, regardless
of the number of outgoing edges at individual vertices. -/
theorem optimum_attained_and_le (c : ∀ q, Out q → ℝ) (q : Q) (n : ℕ) :
    (∃ p : Walk Out target q, p.length = n ∧ Walk.cost Out target c p = optimum Out target c q n) ∧
    ∀ p : Walk Out target q, p.length = n → optimum Out target c q n ≤ Walk.cost Out target c p := by
  classical
  constructor
  · obtain ⟨w, hl, hc⟩ := bellman_attained (policyNext Out target) (policyCost Out c) n q
    exact ⟨decode Out target q w, (decode_length Out target q w).trans hl,
      (decode_cost Out target c q w).trans hc⟩
  · intro p hp
    have h := bellman_le_word (policyNext Out target) (policyCost Out c) q (encode Out target p)
    simpa only [optimum, encode_length, hp, encode_cost] using h

/-- The minimum mean is attained by a nonempty closed walk of at most |Q|
edges, and bounds the mean of every nonempty closed walk in the multigraph. -/
theorem minimum_closed_walk (c : ∀ q, Out q → ℝ) :
    (∃ q, ∃ p : Walk Out target q, 0 < p.length ∧ p.length ≤ Fintype.card Q ∧
      p.finish = q ∧ Walk.cost Out target c p / (p.length : ℝ) = minimumMean Out target c) ∧
    ∀ q (p : Walk Out target q), 0 < p.length → p.finish = q →
      minimumMean Out target c ≤ Walk.cost Out target c p / (p.length : ℝ) := by
  classical
  constructor
  · obtain ⟨q, w, hl, hp, hf, hc⟩ := minimum_cycle_exists
      (policyNext Out target) (policyCost Out c)
    refine ⟨q, decode Out target q w, ?_, ?_, ?_, ?_⟩
    · simpa only [decode_length] using hp
    · simpa only [decode_length] using hl
    · simpa only [decode_finish] using hf
    · rw [decode_cost, decode_length, hc]
      have hne : (w.length : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp)
      dsimp [minimumMean]
      field_simp
  · intro q p hp hf
    have h := closed_word_cost_lower (policyNext Out target) (policyCost Out c) q
      (encode Out target p) (by simpa only [encode_finish] using hf)
    rw [encode_length, encode_cost] at h
    apply (le_div_iff₀ (show (0 : ℝ) < p.length by exact_mod_cast hp)).2
    simpa only [minimumMean, mul_comm] using h

theorem optimum_average_tendsto (c : ∀ q, Out q → ℝ) (q₀ : Q)
    (hreach : ∀ q, ∃ p : Walk Out target q₀, p.finish = q) :
    Filter.Tendsto (fun n : ℕ => optimum Out target c q₀ n / (n : ℝ)) Filter.atTop
      (nhds (minimumMean Out target c)) := by
  classical
  apply bellman_average_tendsto
  intro q
  obtain ⟨p, hp⟩ := hreach q
  exact ⟨encode Out target p, (encode_finish Out target p).trans hp⟩

end LinearInputCurveWordDirectedGraph
