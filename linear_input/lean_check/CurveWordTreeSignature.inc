/-!
Tree-walk cancellation for genuine signatures of straight segments. This is
an algebraic ingredient of the BV tree-signature implication; approximation
of an arbitrary height-coded BV path is a separate proof obligation.
-/

noncomputable section

namespace LinearInputCurveWordTreeSignature

open LinearInputCurveWordSignature LinearInputCurveWordFormalSeries
open LinearInputCurveWordFriedrichs LinearInputCurveWordReparametrization

def walkWeight {V M : Type*} [Monoid M] {G : SimpleGraph V} (W : V → V → M) :
    {u v : V} → G.Walk u v → M
  | _, _, .nil => 1
  | u, _, .cons (v := v) _ p => W u v * walkWeight W p

theorem walkWeight_append {V M : Type*} [Monoid M] {G : SimpleGraph V}
    (W : V → V → M) {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    walkWeight W (p.append q) = walkWeight W p * walkWeight W q := by
  induction p with
  | nil => simp [walkWeight]
  | cons e p ih => simp [walkWeight, ih, mul_assoc]

theorem walkWeight_concat {V M : Type*} [Monoid M] {G : SimpleGraph V}
    (W : V → V → M) {u v w : V} (p : G.Walk u v) (e : G.Adj v w) :
    walkWeight W (p.concat e) = walkWeight W p * W v w := by
  rw [SimpleGraph.Walk.concat_eq_append, walkWeight_append]
  simp [walkWeight]

def rootPath {V : Type*} {G : SimpleGraph V} (hG : G.IsTree) (r v : V) : G.Path r v :=
  ⟨(hG.existsUnique_path r v).choose, (hG.existsUnique_path r v).choose_spec.1⟩

def vertexWeight {V M : Type*} [Monoid M] {G : SimpleGraph V}
    (hG : G.IsTree) (W : V → V → M) (r v : V) : M :=
  walkWeight W (rootPath hG r v).val

/-- The edge weights on a tree are the increments of an actual root-path
weight, provided opposite orientations cancel. -/
theorem vertexWeight_edge {V M : Type*} [Monoid M] {G : SimpleGraph V}
    (hG : G.IsTree) (W : V → V → M)
    (hinv : ∀ u v, G.Adj u v → W v u * W u v = 1)
    (r : V) {u v : V} (e : G.Adj u v) :
    vertexWeight hG W r u * W u v = vertexWeight hG W r v := by
  classical
  let p := rootPath hG r u
  let q := rootPath hG r v
  change walkWeight W p.val * W u v = walkWeight W q.val
  by_cases hu : u ∈ q.val.support
  · have he := hG.isAcyclic.path_concat p.property q.property e hu
    rw [he, walkWeight_concat]
  · have hv := hG.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath
      p.property q.property e hu
    have he := hG.isAcyclic.path_concat q.property p.property e.symm hv
    rw [he, walkWeight_concat, mul_assoc, hinv u v e, mul_one]

theorem vertexWeight_walk {V M : Type*} [Monoid M] {G : SimpleGraph V}
    (hG : G.IsTree) (W : V → V → M)
    (hinv : ∀ u v, G.Adj u v → W v u * W u v = 1)
    (r : V) {u v : V} (p : G.Walk u v) :
    vertexWeight hG W r u * walkWeight W p = vertexWeight hG W r v := by
  induction p with
  | nil => simp [walkWeight]
  | cons e p ih =>
    rw [walkWeight, ← mul_assoc, vertexWeight_edge hG W hinv r e]
    exact ih

/-- Every closed walk on a graph-theoretic tree has weight one. This is a
general theorem, not a finite enumeration of selected loops. -/
theorem tree_closed_walk_weight {V M : Type*} [Monoid M] {G : SimpleGraph V}
    (hG : G.IsTree) (W : V → V → M)
    (hinv : ∀ u v, G.Adj u v → W v u * W u v = 1)
    {r : V} (p : G.Walk r r) : walkWeight W p = 1 := by
  have he := vertexWeight_walk hG W hinv r p
  have hr : vertexWeight hG W r r = 1 := by
    unfold vertexWeight
    rw [SimpleGraph.Path.loop_eq (rootPath hG r r)]
    rfl
  simpa only [hr, one_mul] using he

theorem walkWeight_map {V U M : Type*} [Monoid M] {G : SimpleGraph V} {H : SimpleGraph U}
    (W : U → U → M) (f : G →g H) {u v : V} (p : G.Walk u v) :
    walkWeight W (p.map f) = walkWeight (fun u v => W (f u) (f v)) p := by
  induction p with
  | nil => rfl
  | cons e p ih => simp [walkWeight, ih]

theorem acyclic_closed_walk_weight {V M : Type*} [Monoid M] {G : SimpleGraph V}
    (hG : G.IsAcyclic) (W : V → V → M)
    (hinv : ∀ u v, G.Adj u v → W v u * W u v = 1)
    {r : V} (p : G.Walk r r) : walkWeight W p = 1 := by
  have hT : p.toSubgraph.coe.IsTree :=
    ⟨p.toSubgraph_connected.coe, hG.subgraph p.toSubgraph⟩
  have he := tree_closed_walk_weight hT
    (fun u v => W u.val v.val)
    (fun u v huv => hinv u.val v.val (p.toSubgraph.adj_sub huv)) p.mapToSubgraph
  calc
    walkWeight W p = walkWeight W (p.mapToSubgraph.map p.toSubgraph.hom) :=
      congrArg (walkWeight W) p.map_mapToSubgraph_hom.symm
    _ = walkWeight (fun u v => W (p.toSubgraph.hom u) (p.toSubgraph.hom v)) p.mapToSubgraph :=
      walkWeight_map W p.toSubgraph.hom p.mapToSubgraph
    _ = 1 := he

/-- Maximum-peak elimination: if heights change along edges and a vertex has
at most one lower neighbor, then no graph cycle exists. -/
theorem acyclic_of_unique_lower_neighbor {V : Type*} {G : SimpleGraph V}
    (H : V → ℝ) (hne : ∀ u v, G.Adj u v → H u ≠ H v)
    (hlower : ∀ v u w, G.Adj v u → G.Adj v w → H u < H v → H w < H v → u = w) :
    G.IsAcyclic := by
  classical
  intro r p hp
  obtain ⟨v, hv, hmax⟩ := p.support.toFinset.exists_max_image H
    ⟨r, List.mem_toFinset.mpr p.start_mem_support⟩
  have hv' : v ∈ p.support := List.mem_toFinset.mp hv
  let q := p.rotate v hv'
  have hq : q.IsCycle := hp.rotate hv'
  have hqnon : ¬q.Nil := SimpleGraph.Walk.not_nil_iff_lt_length.mpr (by
    have := hq.three_le_length
    omega)
  have he1 := q.adj_snd hqnon
  have he2 := (q.adj_penultimate hqnon).symm
  have h1 : H q.snd ≤ H v := hmax q.snd (List.mem_toFinset.mpr
    ((p.mem_support_rotate_iff v hv').mp (q.getVert_mem_support 1)))
  have h2 : H q.penultimate ≤ H v := hmax q.penultimate (List.mem_toFinset.mpr
    ((p.mem_support_rotate_iff v hv').mp (q.getVert_mem_support (q.length - 1))))
  have hlt1 : H q.snd < H v := lt_of_le_of_ne h1 (hne _ _ he1.symm)
  have hlt2 : H q.penultimate < H v := lt_of_le_of_ne h2 (hne _ _ he2.symm)
  exact hq.snd_ne_penultimate (hlower v _ _ he1 he2 hlt1 hlt2)

theorem signature_same {ι : Type*} (v : ι → ℝ → ℝ) (a : ℝ) :
    signature v a a = unitSeries := by
  funext w
  cases w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w i =>
    simp [signature, List.reverse_append, reverseIntegral, unitSeries]
    cases w <;> rfl

/-- An edge weight is the entire coefficient series of an actual straight
segment with constant coordinate velocity, defined by iterated integrals. -/
def segmentSignature {ι : Type*} (x y : ι → ℝ) : TensorSeries ι :=
  signature (fun i _ => y i - x i) 0 1

theorem segmentSignature_reverse {ι : Type*} (x y : ι → ℝ) :
    segmentSignature y x = signature (fun i _ => y i - x i) 1 0 := by
  funext w
  have he := signature_reverse_time (fun _ : ι => continuous_const)
    (v := fun i _ => y i - x i) 0 1 w
  simpa only [neg_sub, segmentSignature] using he

theorem segmentSignature_cancel {ι : Type*} (x y : ι → ℝ) :
    segmentSignature x y * segmentSignature y x = 1 := by
  change product (segmentSignature x y) (segmentSignature y x) = unitSeries
  rw [segmentSignature_reverse x y]
  change product (signature (fun i _ => y i - x i) 0 1)
    (signature (fun i _ => y i - x i) 1 0) = unitSeries
  rw [← signature_product (fun _ => continuous_const), signature_same]

/-- The product of actual straight-segment signatures around every closed
walk on every tree is the unit series, at all word degrees. -/
theorem tree_segment_signature_cancel {ι V : Type*} {G : SimpleGraph V}
    (hG : G.IsTree) (x : V → ι → ℝ) {r : V} (p : G.Walk r r) :
    walkWeight (fun u v => segmentSignature (x u) (x v)) p = (1 : TensorSeries ι) :=
  tree_closed_walk_weight hG _ (fun u v _ => segmentSignature_cancel (x v) (x u)) p

theorem height_walk_segment_signature_cancel {ι V : Type*} {G : SimpleGraph V}
    (H : V → ℝ) (hne : ∀ u v, G.Adj u v → H u ≠ H v)
    (hlower : ∀ v u w, G.Adj v u → G.Adj v w → H u < H v → H w < H v → u = w)
    (x : V → ι → ℝ) {r : V} (p : G.Walk r r) :
    walkWeight (fun u v => segmentSignature (x u) (x v)) p = (1 : TensorSeries ι) :=
  acyclic_closed_walk_weight (acyclic_of_unique_lower_neighbor H hne hlower) _
    (fun u v _ => segmentSignature_cancel (x v) (x u)) p

def sequenceWeight {V M : Type*} [Monoid M] (W : V → V → M) (x : ℕ → V) : ℕ → M
  | 0 => 1
  | n + 1 => sequenceWeight W x n * W (x n) (x (n + 1))

theorem exists_walk_sequenceWeight {V M : Type*} [Monoid M] {G : SimpleGraph V}
    (W : V → V → M) (hdiag : ∀v, W v v = 1) (x : ℕ → V) (n : ℕ)
    (hedge : ∀i < n, x i = x (i + 1) ∨ G.Adj (x i) (x (i + 1))) :
    ∃p : G.Walk (x 0) (x n), walkWeight W p = sequenceWeight W x n := by
  induction n with
  | zero => exact ⟨.nil, rfl⟩
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih (fun i hi => hedge i (Nat.lt_trans hi (Nat.lt_succ_self n)))
    rcases hedge n (Nat.lt_succ_self n) with he | he
    · rw [sequenceWeight, ← he, hdiag, mul_one]
      exact ⟨p, hp⟩
    · exact ⟨p.concat he, by rw [walkWeight_concat, hp]; rfl⟩

/-- Repeated vertices cause stationary edges and need not be discarded:
every finite closed sequence of adjacent-or-equal vertices has unit weight
in an acyclic graph. -/
theorem acyclic_closed_sequence_weight {V M : Type*} [Monoid M] {G : SimpleGraph V}
    (hG : G.IsAcyclic) (W : V → V → M) (hdiag : ∀v, W v v = 1)
    (hinv : ∀u v, G.Adj u v → W v u * W u v = 1) (x : ℕ → V) (n : ℕ)
    (hedge : ∀i < n, x i = x (i + 1) ∨ G.Adj (x i) (x (i + 1)))
    (hclosed : x n = x 0) : sequenceWeight W x n = 1 := by
  obtain ⟨p, hp⟩ := exists_walk_sequenceWeight W hdiag x n hedge
  have he : ∀q : G.Walk (x 0) (x n), walkWeight W q = 1 := by
    rw [hclosed]
    exact fun q => acyclic_closed_walk_weight hG W hinv q
  exact hp.symm.trans (he p)

theorem segmentSignature_self {ι : Type*} (x : ι → ℝ) :
    segmentSignature x x = (1 : TensorSeries ι) := by
  change signature (fun i _ => x i - x i) 0 1 = unitSeries
  funext w
  cases w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w i =>
    simp [signature, List.reverse_append, reverseIntegral, unitSeries]
    cases w <;> rfl

theorem acyclic_closed_segment_sequence {ι V : Type*} {G : SimpleGraph V}
    (hG : G.IsAcyclic) (f : V → ι → ℝ) (x : ℕ → V) (n : ℕ)
    (hedge : ∀i < n, x i = x (i + 1) ∨ G.Adj (x i) (x (i + 1)))
    (hclosed : x n = x 0) :
    sequenceWeight (fun u v => segmentSignature (f u) (f v)) x n =
      (1 : TensorSeries ι) :=
  acyclic_closed_sequence_weight hG _ (fun v => segmentSignature_self (f v))
    (fun u v _ => segmentSignature_cancel (f v) (f u)) x n hedge hclosed

end LinearInputCurveWordTreeSignature
