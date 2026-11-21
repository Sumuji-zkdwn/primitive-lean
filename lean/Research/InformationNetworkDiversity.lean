import Mathlib.Tactic

/-!
# Finite information networks: structure, observation, and relative bits

Six labelled vertices, with undirected edges stored once as ordered endpoint
pairs.  The computational distance is the first successful bounded-reachability
query among 0,...,5, with 6 as a disconnected sentinel.  Every numerical
certificate below concerns the explicit connected six-vertex instances.

`encode` forgets absolute vertex bits but retains their edge XORs.  The
factorization lemmas make precise when a query or update can be performed
on the encoded type.  No general entropy/diversity optimality is asserted.
-/

namespace InformationNetworkDiversity

abbrev Vertex := Fin 6
abbrev Edge := Vertex × Vertex
abbrev Config := Vertex → Bool

private def vertices : List Vertex := [0, 1, 2, 3, 4, 5]
private def pairs : List Edge :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5),
   (1, 2), (1, 3), (1, 4), (1, 5),
   (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)]

/-- Undirected adjacency, even though an edge is stored in one orientation. -/
def adjacent (es : List Edge) (u v : Vertex) : Bool :=
  es.contains (u, v) || es.contains (v, u)

def degree (es : List Edge) (u : Vertex) : Nat :=
  (vertices.filter (adjacent es u)).length

def degrees (es : List Edge) : List Nat := vertices.map (degree es)

/-- Number of vertices of each degree 0,...,5; insensitive to vertex names. -/
def degreeHistogram (es : List Edge) : List Nat :=
  ([0, 1, 2, 3, 4, 5] : List Nat).map
    (fun k => ((degrees es).filter (fun d => d == k)).length)

/-- Freeman centralization numerator. Divide by (6-1)*(6-2) = 20. -/
def hubNumerator (es : List Edge) : Nat :=
  let top := (degrees es).foldl max 0
  ((degrees es).map (fun d => top - d)).sum

/-- Path reachability by at most k edges, not a spatial distance. -/
def reachableWithin (es : List Edge) (u v : Vertex) : Nat → Bool
  | 0 => u == v
  | k + 1 => reachableWithin es u v k ||
      vertices.any (fun w => reachableWithin es u w k && adjacent es w v)

/-- The first reachable radius ≤5, or sentinel 6 for an unreachable pair. -/
def boundedDistance (es : List Edge) (u v : Vertex) : Nat :=
  if reachableWithin es u v 0 then 0
  else if reachableWithin es u v 1 then 1
  else if reachableWithin es u v 2 then 2
  else if reachableWithin es u v 3 then 3
  else if reachableWithin es u v 4 then 4
  else if reachableWithin es u v 5 then 5
  else 6

def distanceSum (es : List Edge) : Nat :=
  (pairs.map (fun e => boundedDistance es e.1 e.2)).sum

/-- Distance histogram at lengths 1,...,5. -/
def distanceHistogram (es : List Edge) : List Nat :=
  ([1, 2, 3, 4, 5] : List Nat).map
    (fun k => (pairs.filter (fun e => boundedDistance es e.1 e.2 == k)).length)

/-- A purely spatial measurement, requiring an extra vertex placement. -/
def spatialLongEdges (pos : Vertex → Nat) (es : List Edge) : Nat :=
  (es.filter (fun e => decide (Nat.dist (pos e.1) (pos e.2) ≥ 3))).length

private def naturalPosition (v : Vertex) : Nat := v.val
private def zeroLongPosition (v : Vertex) : Nat :=
  match v.val with
  | 0 => 1 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 0 | _ => 5
private def allLongPosition (v : Vertex) : Nat :=
  match v.val with
  | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 5 | 4 => 3 | _ => 2

/-- The two 6-vertex networks in the November 20 example. -/
def graphA : List Edge :=
  [(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (3, 5)]

def graphB : List Edge :=
  [(0, 2), (1, 2), (1, 3), (1, 4), (2, 4), (3, 5)]

/-- Vertex-wise degrees and spatial long-edge count agree, but distance sums differ. -/
def graphC : List Edge :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 3), (2, 5)]
def graphD : List Edge :=
  [(0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3)]

/-- Same distance histogram and long-edge count but different hub centralization. -/
def graphH : List Edge :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5)]
def graphI : List Edge :=
  [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 5)]

/-- Same labelled degrees and distance histogram, different spatial length. -/
def graphJ : List Edge := graphH
def graphK : List Edge :=
  [(0, 1), (0, 2), (0, 4), (0, 5), (1, 2), (1, 3)]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem AB_same_degree_histogram :
    degreeHistogram graphA = degreeHistogram graphB := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem AB_distance_sums :
    distanceSum graphA = 27 ∧ distanceSum graphB = 29 := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem AB_distance_histograms :
    distanceHistogram graphA = [6, 6, 3, 0, 0] ∧
    distanceHistogram graphB = [6, 5, 3, 1, 0] := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem AB_same_hub_numerator :
    hubNumerator graphA = 6 ∧ hubNumerator graphB = 6 := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem AB_spatial_long_counts :
    spatialLongEdges naturalPosition graphA = 2 ∧
    spatialLongEdges naturalPosition graphB = 1 := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem CD_same_degrees_long_different_distance :
    degrees graphC = degrees graphD ∧
    spatialLongEdges naturalPosition graphC = 3 ∧
    spatialLongEdges naturalPosition graphD = 3 ∧
    distanceSum graphC = 27 ∧ distanceSum graphD = 26 := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem HI_same_distance_long_different_hub :
    distanceHistogram graphH = distanceHistogram graphI ∧
    spatialLongEdges naturalPosition graphH = 3 ∧
    spatialLongEdges naturalPosition graphI = 3 ∧
    hubNumerator graphH = 12 ∧ hubNumerator graphI = 6 := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem JK_same_degrees_distance_different_long :
    degrees graphJ = degrees graphK ∧
    distanceHistogram graphJ = distanceHistogram graphK ∧
    spatialLongEdges naturalPosition graphJ = 3 ∧
    spatialLongEdges naturalPosition graphK = 2 := by decide

/-- The spatial placement changes long edges without changing the graph. -/
theorem A_position_changes_long_edges :
    spatialLongEdges zeroLongPosition graphA = 0 ∧
    spatialLongEdges allLongPosition graphA = 6 := by decide

private def connectedFromZero (es : List Edge) : Bool :=
  vertices.all (fun v => reachableWithin es 0 v 5)

private def remove02 (es : List Edge) : List Edge :=
  es.filter (fun e => e != (0, 2))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem AB_current_connected_but_delete_distinguishes :
    connectedFromZero graphA = true ∧
    connectedFromZero graphB = true ∧
    connectedFromZero (remove02 graphA) = true ∧
    connectedFromZero (remove02 graphB) = false := by decide

/-! ## Relational information type -/

/-- XOR of endpoint information on one edge. -/
def edgeBit (x : Config) (e : Edge) : Bool := Bool.xor (x e.1) (x e.2)

def encode (es : List Edge) (x : Config) : List Bool := es.map (edgeBit x)

def invertAll (x : Config) : Config := fun v => !x v

/-- Flipping all source bits is invisible to every edge-XOR observer. -/
theorem edgeBit_invertAll (x : Config) (e : Edge) :
    edgeBit (invertAll x) e = edgeBit x e := by
  rcases e with ⟨u, v⟩
  cases h₁ : x u <;> cases h₂ : x v <;>
    simp [edgeBit, invertAll, h₁, h₂]

theorem encode_invertAll (es : List Edge) (x : Config) :
    encode es (invertAll x) = encode es x := by
  induction es with
  | nil => rfl
  | cons e tail ih => simp [encode, edgeBit_invertAll, ih]

def allZero : Config := fun _ => false
def allOne : Config := fun _ => true

/-- A global bit flip produces a two-point fibre on any nonempty vertex set. -/
theorem encode_not_injective (es : List Edge) : ¬ Function.Injective (encode es) := by
  intro inj
  have hz : invertAll allZero = allOne := by
    funext v
    rfl
  have hsame : encode es allZero = encode es allOne := by
    rw [← hz]
    exact (encode_invertAll es allZero).symm
  have heq := inj hsame
  have h0 := congrArg (fun x : Config => x (0 : Vertex)) heq
  have hf : false = true := by simpa [allZero, allOne] using h0
  cases hf

/-- XOR along a two-edge path recovers the endpoint relation. -/
theorem edgeBit_chain (x : Config) (u v w : Vertex) :
    edgeBit x (u, w) = Bool.xor (edgeBit x (u, v)) (edgeBit x (v, w)) := by
  cases h₁ : x u <;> cases h₂ : x v <;> cases h₃ : x w <;>
    simp [edgeBit, h₁, h₂, h₃]

/-- Equality of encoded lists gives equality of each listed edge bit. -/
theorem encode_eq_edge (es : List Edge) (x y : Config) :
    encode es x = encode es y → ∀ e ∈ es, edgeBit x e = edgeBit y e := by
  induction es with
  | nil =>
      intro _ e he
      cases he
  | cons a tail ih =>
      intro h e he
      have hp : edgeBit x a = edgeBit y a ∧ encode tail x = encode tail y := by
        simpa [encode] using h
      rcases List.mem_cons.mp he with rfl | ht
      · exact hp.1
      · exact ih hp.2 e ht

/-- In A, the relation between distant vertices 0 and 5 is observable. -/
theorem A_relative_05_observable (x y : Config)
    (h : encode graphA x = encode graphA y) :
    edgeBit x (0, 5) = edgeBit y (0, 5) := by
  have h03 : edgeBit x (0, 3) = edgeBit y (0, 3) :=
    encode_eq_edge graphA x y h (0, 3) (by decide)
  have h35 : edgeBit x (3, 5) = edgeBit y (3, 5) :=
    encode_eq_edge graphA x y h (3, 5) (by decide)
  calc
    edgeBit x (0, 5) = Bool.xor (edgeBit x (0, 3)) (edgeBit x (3, 5)) :=
      edgeBit_chain x 0 3 5
    _ = Bool.xor (edgeBit y (0, 3)) (edgeBit y (3, 5)) := by rw [h03, h35]
    _ = edgeBit y (0, 5) := (edgeBit_chain y 0 3 5).symm

/-! ## Quotient criteria: exactly which forgotten distinctions matter? -/

/-- A query factors through a summary precisely when it is constant on fibres. -/
def FactorsThrough {α β γ : Type*} (summary : α → β) (query : α → γ) : Prop :=
  ∀ x y, summary x = summary y → query x = query y

/-- A fibre-invariant query induces a function on the *reachable* summaries. -/
theorem factorsThrough_iff_range {α β γ : Type*}
    (summary : α → β) (query : α → γ) :
    FactorsThrough summary query ↔
      ∃ f : Set.range summary → γ,
        ∀ x, f ⟨summary x, ⟨x, rfl⟩⟩ = query x := by
  classical
  constructor
  · intro h
    let f : Set.range summary → γ := fun r => query (Classical.choose r.property)
    refine ⟨f, ?_⟩
    intro x
    exact h (Classical.choose (show ∃ a, summary a = summary x from ⟨x, rfl⟩)) x
      (Classical.choose_spec (show ∃ a, summary a = summary x from ⟨x, rfl⟩))
  · rintro ⟨f, hf⟩ x y hxy
    calc
      query x = f ⟨summary x, ⟨x, rfl⟩⟩ := (hf x).symm
      _ = f ⟨summary y, ⟨y, rfl⟩⟩ := congrArg f (Subtype.ext hxy)
      _ = query y := hf y

/-- Criterion for autonomous dynamics of a compressed state. -/
theorem update_factors_iff_range {α β : Type*}
    (summary : α → β) (update : α → α) :
    (∀ x y, summary x = summary y → summary (update x) = summary (update y)) ↔
      ∃ step : Set.range summary → Set.range summary,
        ∀ x, (step ⟨summary x, ⟨x, rfl⟩⟩).1 = summary (update x) := by
  classical
  constructor
  · intro h
    let step : Set.range summary → Set.range summary := fun r =>
      ⟨summary (update (Classical.choose r.property)),
       ⟨update (Classical.choose r.property), rfl⟩⟩
    refine ⟨step, ?_⟩
    intro x
    exact h (Classical.choose (show ∃ a, summary a = summary x from ⟨x, rfl⟩)) x
      (Classical.choose_spec (show ∃ a, summary a = summary x from ⟨x, rfl⟩))
  · rintro ⟨step, hs⟩ x y hxy
    calc
      summary (update x) = (step ⟨summary x, ⟨x, rfl⟩⟩).1 := (hs x).symm
      _ = (step ⟨summary y, ⟨y, rfl⟩⟩).1 :=
        congrArg (fun s : Set.range summary => (step s).1) (Subtype.ext hxy)
      _ = summary (update y) := hs y

/-- Applying a fixed XOR mask to vertices respects encoded equivalence. -/
def xorMask (x mask : Config) : Config := fun v => Bool.xor (x v) (mask v)

theorem edgeBit_mask (x mask : Config) (e : Edge) :
    edgeBit (xorMask x mask) e = Bool.xor (edgeBit x e) (edgeBit mask e) := by
  rcases e with ⟨u, v⟩
  cases h₁ : x u <;> cases h₂ : x v <;>
    cases h₃ : mask u <;> cases h₄ : mask v <;>
      simp [edgeBit, xorMask, h₁, h₂, h₃, h₄]

theorem xorMask_descends (es : List Edge) (mask x y : Config) :
    encode es x = encode es y →
      encode es (xorMask x mask) = encode es (xorMask y mask) := by
  induction es with
  | nil =>
      intro _
      rfl
  | cons e tail ih =>
      intro h
      have hp : edgeBit x e = edgeBit y e ∧ encode tail x = encode tail y := by
        simpa [encode] using h
      have head : edgeBit (xorMask x mask) e = edgeBit (xorMask y mask) e := by
        rw [edgeBit_mask, edgeBit_mask, hp.1]
      exact congrArg₂ List.cons head (ih hp.2)

/-- A reset is not a well-defined update of the edge-information type. -/
def resetZero (x : Config) : Config :=
  fun v => if v = 0 then false else x v

theorem resetZero_not_descending :
    ¬ FactorsThrough (encode graphA) (fun x => encode graphA (resetZero x)) := by
  intro h
  have hz : invertAll allZero = allOne := by funext v; rfl
  have hs : encode graphA allZero = encode graphA allOne := by
    rw [← hz]
    exact (encode_invertAll graphA allZero).symm
  have hsame := h allZero allOne hs
  have hdiff : encode graphA (resetZero allZero) ≠ encode graphA (resetZero allOne) := by
    decide
  exact hdiff hsame

end InformationNetworkDiversity
