/-!
F0: idempotent retractions, compatible splitting and composition.
The equations A and B are explicit hypotheses, not silently imposed axioms.
-/

noncomputable section
open Function Set Real

namespace LinearInputF0

attribute [local instance] Classical.propDecidable

def Idempotent {α : Type*} (K : α → α) : Prop := ∀ x, K (K x) = K x

abbrev Fixed {α : Type*} (K : α → α) := {a : α // K a = a}

abbrev Fiber {α : Type*} (K : α → α) (a : Fixed K) := {x : α // K x = a.val}

def liftK {α I : Type*} (K : α → α) (v : I → α) : I → α := fun i => K (v i)

def Compatible {α I : Type*} (K : α → α) (S : α → I → α) : Prop :=
  ∀ x i, S (K x) i = K (S x i)

def Reconstructs {α I : Type*} (S : α → I → α) (C : (I → α) → α) : Prop :=
  ∀ x, C (S x) = x

def step {α I : Type*} (K : α → α) (S : α → I → α) (C : (I → α) → α) (x : α) : α :=
  K (C (liftK K (S x)))

theorem fixed_iff_in_range {α : Type*} {K : α → α} (hK : Idempotent K) (x : α) :
    K x = x ↔ x ∈ Set.range K := by
  constructor
  · intro h; exact ⟨x, h⟩
  · rintro ⟨a, rfl⟩; exact hK a

def fiberDecomposition {α : Type*} {K : α → α} (hK : Idempotent K) :
    α ≃ Σ a : Fixed K, Fiber K a where
  toFun x := ⟨⟨K x, hK x⟩, ⟨x, rfl⟩⟩
  invFun p := p.2.val
  left_inv x := rfl
  right_inv := by
    rintro ⟨⟨a, ha⟩, ⟨x, hx⟩⟩
    change K x = a at hx
    subst a
    rfl

theorem fiber_card_sum {α : Type*} [Fintype α] {K : α → α} (hK : Idempotent K) :
    Fintype.card α = ∑ a : Fixed K, Nat.card (Fiber K a) := by
  classical
  simpa only [Nat.card_eq_fintype_card, Fintype.card_sigma] using Fintype.card_congr (fiberDecomposition hK)

theorem fiber_nonempty {α : Type*} {K : α → α} (a : Fixed K) : Nonempty (Fiber K a) :=
  ⟨⟨a.val, a.property⟩⟩

theorem liftK_idempotent {α I : Type*} {K : α → α} (hK : Idempotent K) :
    Idempotent (liftK (I := I) K) := by
  intro v; funext i; exact hK (v i)

theorem compatible_iff_lift {α I : Type*} (K : α → α) (S : α → I → α) :
    Compatible K S ↔ ∀ x, liftK K (S x) = S (K x) := by
  constructor
  · intro h x; funext i; exact (h x i).symm
  · intro h x i; exact (congrFun (h x) i).symm

theorem compatible_coarse_eq {α I : Type*} {K : α → α} {S : α → I → α}
    (hS : Compatible K S) {x y : α} (hxy : K x = K y) :
    liftK K (S x) = liftK K (S y) := by
  rw [(compatible_iff_lift K S).mp hS, (compatible_iff_lift K S).mp hS, hxy]

theorem diagonal_compatible {α I : Type*} (K : α → α) :
    Compatible K (fun x (_ : I) => x) := by intro x i; rfl

theorem indistinguishable_iff {α I : Type*} [Nonempty I] (K : α → α) (x y : α) :
    K x = K y ↔ ∀ S : α → I → α, Compatible K S → liftK K (S x) = liftK K (S y) := by
  constructor
  · intro h S hS; exact compatible_coarse_eq hS h
  · intro h
    exact congrFun (h (fun z (_ : I) => z) (diagonal_compatible K)) (Classical.choice inferInstance)

theorem step_fixed {α I : Type*} {K : α → α} (hK : Idempotent K)
    (S : α → I → α) (C : (I → α) → α) (x : α) :
    K (step K S C x) = step K S C x := hK _

theorem step_factor {α I : Type*} {K : α → α} {S : α → I → α}
    (hS : Compatible K S) (C : (I → α) → α) (x : α) :
    step K S C x = K (C (S (K x))) := by
  rw [step, (compatible_iff_lift K S).mp hS]

theorem step_absorbs_K {α I : Type*} {K : α → α} (hK : Idempotent K)
    {S : α → I → α} (hS : Compatible K S) (C : (I → α) → α) (x : α) :
    step K S C (K x) = step K S C x := by
  rw [step_factor hS, step_factor hS, hK]

theorem step_equal_on_fibers {α I : Type*} {K : α → α} {S : α → I → α}
    (hS : Compatible K S) (C : (I → α) → α) {x y : α} (hxy : K x = K y) :
    step K S C x = step K S C y := by rw [step_factor hS, step_factor hS, hxy]

theorem reconstruction_injective {α I : Type*} {S : α → I → α} {C : (I → α) → α}
    (hA : Reconstructs S C) : Function.Injective S := by
  intro x y h
  calc x = C (S x) := (hA x).symm
       _ = C (S y) := congrArg C h
       _ = y := hA y

theorem A_B_collapse {α I : Type*} {K : α → α} (hK : Idempotent K)
    {S : α → I → α} {C : (I → α) → α} (hA : Reconstructs S C) (hB : Compatible K S) :
    step K S C = K := by
  funext x
  rw [step_factor hB, hA, hK]

theorem noncollapse_requires_failure {α I : Type*} {K : α → α} (hK : Idempotent K)
    {S : α → I → α} {C : (I → α) → α} (hT : step K S C ≠ K) :
    ¬ Reconstructs S C ∨ ¬ Compatible K S := by
  classical
  by_cases hA : Reconstructs S C
  · exact Or.inr (fun hB => hT (A_B_collapse hK hA hB))
  · exact Or.inl hA

theorem collapse_idempotent {α I : Type*} {K : α → α} (hK : Idempotent K)
    {S : α → I → α} {C : (I → α) → α} (hA : Reconstructs S C) (hB : Compatible K S) :
    Idempotent (step K S C) := by rw [A_B_collapse hK hA hB]; exact hK

theorem idempotent_iterate_positive {α : Type*} {K : α → α} (hK : Idempotent K)
    (n : ℕ) (x : α) : K^[n + 1] x = K x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, hK]

theorem positive_iterate_fixed {α I : Type*} {K : α → α} (hK : Idempotent K)
    (S : α → I → α) (C : (I → α) → α) (n : ℕ) (x : α) :
    K ((step K S C)^[n + 1] x) = (step K S C)^[n + 1] x := by
  rw [Function.iterate_succ_apply']
  exact step_fixed hK S C _

theorem periodic_point_fixed {α I : Type*} {K : α → α} (hK : Idempotent K)
    (S : α → I → α) (C : (I → α) → α) {n : ℕ} (hn : 0 < n) {x : α}
    (hp : (step K S C)^[n] x = x) : K x = x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simpa only [hp] using positive_iterate_fixed hK S C m x

theorem periodic_cycle_bound {α I : Type*} [Fintype α] {K : α → α} (hK : Idempotent K)
    (S : α → I → α) (C : (I → α) → α) {p : ℕ} (hp : 0 < p) {x : α}
    (hperiod : (step K S C)^[p] x = x)
    (hdistinct : Function.Injective (fun i : Fin p => (step K S C)^[i.val] x)) :
    p ≤ Nat.card (Fixed K) := by
  classical
  let : Fintype (Fixed K) := Fintype.ofFinite _
  have hfixed : ∀ i : Fin p, K ((step K S C)^[i.val] x) = (step K S C)^[i.val] x := by
    intro i
    cases hi : i.val with
    | zero => simpa only [Function.iterate_zero, id_eq] using periodic_point_fixed hK S C hp hperiod
    | succ m => exact positive_iterate_fixed hK S C m x
  let f : Fin p → Fixed K := fun i => ⟨(step K S C)^[i.val] x, hfixed i⟩
  have hf : Function.Injective f := by
    intro i j h; exact hdistinct (congrArg Subtype.val h)
  simpa [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective f hf

def branchZeroK (m : ℕ) (j : Fin (2 * m + 1)) : Fin (2 * m + 1) :=
  LinearInputBranchFibers.lowLabel m (LinearInputBranchFibers.zeroRepresentative m j)

def branchPiK (m : ℕ) (j : Fin (2 * m + 1)) : Fin (2 * m + 1) :=
  LinearInputBranchFibers.lowLabel m (LinearInputBranchFibers.piRepresentative m j)

theorem branchZeroK_idempotent (m : ℕ) : Idempotent (branchZeroK m) :=
  LinearInputBranchFibers.zero_retraction_idempotent m

theorem branchPiK_idempotent (m : ℕ) : Idempotent (branchPiK m) :=
  LinearInputBranchFibers.pi_retraction_idempotent m

theorem branchZero_kernel (m : ℕ) (j k : Fin (2 * m + 1)) :
    branchZeroK m j = branchZeroK m k ↔
      LinearInputBranchFibers.candidate (2 * m + 1) 0 j =
        LinearInputBranchFibers.candidate (2 * m + 1) 0 k := by
  constructor
  · intro h
    have he := congrArg (LinearInputBranchFibers.candidate (2 * m + 1) 0) h
    simpa only [branchZeroK, LinearInputBranchFibers.candidate_zero_representative] using he
  · intro h
    have he := LinearInputBranchFibers.candidate_zero_low_injective m
      ((LinearInputBranchFibers.candidate_zero_representative m j).trans
        (h.trans (LinearInputBranchFibers.candidate_zero_representative m k).symm))
    exact congrArg (LinearInputBranchFibers.lowLabel m) he

theorem branchPi_kernel (m : ℕ) (j k : Fin (2 * m + 1)) :
    branchPiK m j = branchPiK m k ↔
      LinearInputBranchFibers.candidate (2 * m + 1) π j =
        LinearInputBranchFibers.candidate (2 * m + 1) π k := by
  constructor
  · intro h
    have he := congrArg (LinearInputBranchFibers.candidate (2 * m + 1) π) h
    simpa only [branchPiK, LinearInputBranchFibers.candidate_pi_representative] using he
  · intro h
    have he := LinearInputBranchFibers.candidate_pi_low_injective m
      ((LinearInputBranchFibers.candidate_pi_representative m j).trans
        (h.trans (LinearInputBranchFibers.candidate_pi_representative m k).symm))
    exact congrArg (LinearInputBranchFibers.lowLabel m) he

theorem branchZero_A_B_collapse {I : Type*} (m : ℕ)
    {S : Fin (2 * m + 1) → I → Fin (2 * m + 1)}
    {C : (I → Fin (2 * m + 1)) → Fin (2 * m + 1)}
    (hA : Reconstructs S C) (hB : Compatible (branchZeroK m) S) :
    step (branchZeroK m) S C = branchZeroK m := A_B_collapse (branchZeroK_idempotent m) hA hB

theorem branchPi_A_B_collapse {I : Type*} (m : ℕ)
    {S : Fin (2 * m + 1) → I → Fin (2 * m + 1)}
    {C : (I → Fin (2 * m + 1)) → Fin (2 * m + 1)}
    (hA : Reconstructs S C) (hB : Compatible (branchPiK m) S) :
    step (branchPiK m) S C = branchPiK m := A_B_collapse (branchPiK_idempotent m) hA hB

abbrev Tail {α : Type*} (K : α → α) (a : Fixed K) :=
  {x : α // K x = a.val ∧ x ≠ a.val}

abbrev CommutingMap {α : Type*} (K : α → α) :=
  {s : α → α // ∀ x, s (K x) = K (s x)}

abbrev FiberChoice {α : Type*} (K : α → α) (a : Fixed K) :=
  Σ b : Fixed K, Tail K a → Fiber K b

def encodeCommuting {α : Type*} {K : α → α} (s : CommutingMap K) :
    ∀ a : Fixed K, FiberChoice K a := fun a =>
  ⟨⟨s.val a.val, by have h := s.property a.val; rw [a.property] at h; exact h.symm⟩,
    fun x => ⟨s.val x.val, by have h := s.property x.val; rw [x.property.1] at h; exact h.symm⟩⟩

def decodeChoices {α : Type*} {K : α → α} (hK : Idempotent K)
    (v : ∀ a : Fixed K, FiberChoice K a) (x : α) : α :=
  if h : x = K x then (v ⟨K x, hK x⟩).1.val
  else ((v ⟨K x, hK x⟩).2 ⟨x, rfl, h⟩).val

theorem decodeChoices_fixed {α : Type*} {K : α → α} (hK : Idempotent K)
    (v : ∀ a : Fixed K, FiberChoice K a) (a : Fixed K) :
    decodeChoices hK v a.val = (v a).1.val := by
  have hi : (⟨K a.val, hK a.val⟩ : Fixed K) = a := Subtype.ext a.property
  unfold decodeChoices
  rw [dite_eq_left a.property.symm, hi]

theorem decodeChoices_tail {α : Type*} {K : α → α} (hK : Idempotent K)
    (v : ∀ a : Fixed K, FiberChoice K a) (a : Fixed K) (x : Tail K a) :
    decodeChoices hK v x.val = ((v a).2 x).val := by
  rcases a with ⟨a, ha⟩
  rcases x with ⟨x, hx, hne⟩
  change K x = a at hx
  subst a
  simp only [decodeChoices, dite_eq_right hne]

theorem decodeChoices_commutes {α : Type*} {K : α → α} (hK : Idempotent K)
    (v : ∀ a : Fixed K, FiberChoice K a) (x : α) :
    decodeChoices hK v (K x) = K (decodeChoices hK v x) := by
  have hf := decodeChoices_fixed hK v ⟨K x, hK x⟩
  change decodeChoices hK v (K x) = _ at hf
  rw [hf]
  unfold decodeChoices
  split_ifs with hx
  · exact (v ⟨K x, hK x⟩).1.property.symm
  · exact ((v ⟨K x, hK x⟩).2 ⟨x, rfl, hx⟩).property.symm

theorem decode_encode {α : Type*} {K : α → α} (hK : Idempotent K)
    (s : CommutingMap K) : decodeChoices hK (encodeCommuting s) = s.val := by
  funext x
  unfold decodeChoices
  split_ifs with hx
  · change s.val (K x) = s.val x
    rw [← hx]
  · rfl

theorem subtype_heq {α : Type*} {p q : α → Prop} (hpq : p = q)
    {x : Subtype p} {y : Subtype q} (hxy : x.val = y.val) : HEq x y := by
  subst q
  exact heq_of_eq (Subtype.ext hxy)

theorem encode_decode {α : Type*} {K : α → α} (hK : Idempotent K)
    (v : ∀ a : Fixed K, FiberChoice K a) :
    encodeCommuting ⟨decodeChoices hK v, decodeChoices_commutes hK v⟩ = v := by
  funext a
  have hb : (⟨decodeChoices hK v a.val, by
      have h := decodeChoices_commutes hK v a.val
      rw [a.property] at h
      exact h.symm⟩ : Fixed K) = (v a).1 := Subtype.ext (decodeChoices_fixed hK v a)
  apply Sigma.ext hb
  apply Function.hfunext
  · rfl
  · intro x y hxy
    have he : x = y := eq_of_heq hxy
    subst y
    apply subtype_heq (show (fun z => K z = decodeChoices hK v a.val) =
        (fun z => K z = (v a).1.val) from by rw [decodeChoices_fixed])
    exact decodeChoices_tail hK v a x

def commutingChoicesEquiv {α : Type*} {K : α → α} (hK : Idempotent K) :
    CommutingMap K ≃ (∀ a : Fixed K, FiberChoice K a) where
  toFun := encodeCommuting
  invFun v := ⟨decodeChoices hK v, decodeChoices_commutes hK v⟩
  left_inv s := Subtype.ext (decode_encode hK s)
  right_inv := encode_decode hK

def tailFiberEquiv {α : Type*} {K : α → α} (a : Fixed K) :
    Tail K a ≃ {x : Fiber K a // x ≠ ⟨a.val, a.property⟩} where
  toFun x := ⟨⟨x.val, x.property.1⟩, fun h => x.property.2 (congrArg Subtype.val h)⟩
  invFun x := ⟨x.val.val, x.val.property, fun h => x.property (Subtype.ext h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem tail_card {α : Type*} [Fintype α] {K : α → α} (a : Fixed K) :
    Nat.card (Tail K a) = Nat.card (Fiber K a) - 1 := by
  classical
  rw [Nat.card_congr (tailFiberEquiv a)]
  simp only [Nat.card_eq_fintype_card, ne_eq, Fintype.card_subtype_compl, Fintype.card_subtype_eq]

/-- Counts actual commuting maps, via an explicit equivalence with fiber choices. -/
theorem commuting_map_count {α : Type*} [Fintype α] {K : α → α} (hK : Idempotent K) :
    Nat.card (CommutingMap K) =
      ∏ a : Fixed K, ∑ b : Fixed K, Nat.card (Fiber K b) ^ (Nat.card (Fiber K a) - 1) := by
  classical
  rw [Nat.card_congr (commutingChoicesEquiv hK), Nat.card_pi]
  congr 1
  funext a
  rw [show FiberChoice K a = (Σ b : Fixed K, Tail K a → Fiber K b) from rfl, Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro b _
  rw [Nat.card_fun, tail_card]

def compatibleComponentsEquiv {α I : Type*} (K : α → α) :
    {S : α → I → α // Compatible K S} ≃ (I → CommutingMap K) where
  toFun S i := ⟨fun x => S.val x i, fun x => S.property x i⟩
  invFun s := ⟨fun x i => (s i).val x, fun x i => (s i).property x⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- ZIP formula: each output component independently chooses a commuting map. -/
theorem compatible_split_count {α I : Type*} [Fintype α] [Fintype I]
    {K : α → α} (hK : Idempotent K) :
    Nat.card {S : α → I → α // Compatible K S} =
      ∏ a : Fixed K,
        (∑ b : Fixed K, Nat.card (Fiber K b) ^ (Nat.card (Fiber K a) - 1)) ^ Fintype.card I := by
  classical
  rw [Nat.card_congr (compatibleComponentsEquiv (I := I) K), Nat.card_fun, commuting_map_count hK]
  simp only [Nat.card_eq_fintype_card, Finset.prod_pow]

def exampleK (x : Fin 3) : Fin 3 := if x = 2 then 2 else 0

def exampleBadS (x : Fin 3) (_ : Fin 1) : Fin 3 := if x = 1 then 2 else 0

theorem exampleK_idempotent : Idempotent exampleK := by
  intro x
  by_cases h : x = 2 <;> simp [exampleK, h]

theorem compatible_need_not_equal_raw_outputs :
    Compatible exampleK (fun x (_ : Fin 1) => x) ∧
    exampleK 0 = exampleK 1 ∧
    (fun (_ : Fin 1) => (0 : Fin 3)) ≠ (fun (_ : Fin 1) => (1 : Fin 3)) := by
  refine ⟨diagonal_compatible _, by norm_num [exampleK, Fin.ext_iff], ?_⟩
  intro h
  have he := congrFun h 0
  norm_num [Fin.ext_iff] at he

theorem incompatible_can_separate :
    ¬ Compatible exampleK exampleBadS ∧ exampleK 0 = exampleK 1 ∧
      liftK exampleK (exampleBadS 0) ≠ liftK exampleK (exampleBadS 1) := by
  refine ⟨?_, by norm_num [exampleK, Fin.ext_iff], ?_⟩
  · intro h
    have he := h 1 0
    norm_num [exampleK, exampleBadS, Fin.ext_iff] at he
  · intro h
    have he := congrFun h 0
    norm_num [liftK, exampleK, exampleBadS, Fin.ext_iff] at he

theorem failure_does_not_imply_noncollapse :
    ¬ Reconstructs (fun x (_ : Fin 1) => x) (fun _ => (0 : Fin 3)) ∧
      step (fun (_ : Fin 3) => (0 : Fin 3)) (fun x (_ : Fin 1) => x) (fun _ => 0) =
        (fun _ => 0) := by
  constructor
  · intro h
    have he := h 1
    norm_num [Fin.ext_iff] at he
  · rfl

theorem eventual_collision_bound {α I : Type*} [Fintype α] {K : α → α}
    (hK : Idempotent K) (S : α → I → α) (C : (I → α) → α) (x : α) :
    ∃ i j : ℕ, 1 ≤ i ∧ i < j ∧ j ≤ Nat.card (Fixed K) + 1 ∧
      (step K S C)^[i] x = (step K S C)^[j] x := by
  classical
  let r := Fintype.card (Fixed K)
  let f : Fin (r + 1) → Fixed K := fun i =>
    ⟨(step K S C)^[i.val + 1] x, positive_iterate_fixed hK S C i.val x⟩
  obtain ⟨i, j, hne, he⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp [r])
  have hv := congrArg Subtype.val he
  have hn : i.val ≠ j.val := fun h => hne (Fin.ext h)
  have hi := i.isLt
  have hj := j.isLt
  have hr : Nat.card (Fixed K) = r := Nat.card_eq_fintype_card
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · exact ⟨i.val + 1, j.val + 1, by omega, by omega, by omega, hv⟩
  · exact ⟨j.val + 1, i.val + 1, by omega, by omega, by omega, hv.symm⟩

theorem eventually_periodic {α I : Type*} [Fintype α] {K : α → α}
    (hK : Idempotent K) (S : α → I → α) (C : (I → α) → α) (x : α) :
    ∃ i p : ℕ, 1 ≤ i ∧ 0 < p ∧ ∀ k : ℕ,
      (step K S C)^[i + p + k] x = (step K S C)^[i + k] x := by
  obtain ⟨i, j, hi, hij, _, he⟩ := eventual_collision_bound hK S C x
  refine ⟨i, j - i, hi, by omega, ?_⟩
  intro k
  rw [show i + (j - i) + k = k + j by omega, show i + k = k + i by omega,
    Function.iterate_add_apply, Function.iterate_add_apply, he]

end LinearInputF0
