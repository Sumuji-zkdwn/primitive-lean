import Mathlib

/-!
# Associative exact-set completion for opaque observational quotients

The concrete operation is total and deterministic.  Images of products of
observation fibers give a multivalued operation; this operation is not
necessarily associative, even if the concrete operation is.  Keeping the
actual SET of possible concrete values restores associativity.

This file proves the set-level lifting and a sufficient condition for
associativity of the coarse hyperoperation.  Independent finite examples
certify that the coarse hyperoperation may fail associativity (3 states)
and that it may be associative without faithfully evaluating three
concrete factors (5-state cyclic group).
-/

namespace VoidHyperCompletion

universe u v

variable {α : Type u} {β : Type v}

/-- All possible products of one independently chosen element from each set. -/
def setProd (op : α → α → α) (A B : Set α) : Set α :=
  {z | ∃ a ∈ A, ∃ b ∈ B, op a b = z}

/-- An associative concrete operation induces associative exact-set products. -/
theorem setProd_assoc (op : α → α → α)
    (hassoc : ∀ a b c, op (op a b) c = op a (op b c))
    (A B C : Set α) :
    setProd op (setProd op A B) C =
      setProd op A (setProd op B C) := by
  ext z
  constructor
  · rintro ⟨ab, ⟨a, ha, b, hb, hab⟩, c, hc, habc⟩
    refine ⟨a, ha, op b c, ⟨b, hb, c, hc, rfl⟩, ?_⟩
    calc
      op a (op b c) = op (op a b) c := (hassoc a b c).symm
      _ = op ab c := congrArg (fun t => op t c) hab
      _ = z := habc
  · rintro ⟨a, ha, bc, ⟨b, hb, c, hc, hbc⟩, habc⟩
    refine ⟨op a b, ⟨a, ha, b, hb, rfl⟩, c, hc, ?_⟩
    calc
      op (op a b) c = op a (op b c) := hassoc a b c
      _ = op a bc := congrArg (op a) hbc
      _ = z := habc

/-- Complete an internal set to the union of all observational fibers it touches. -/
def saturate (π : α → β) (A : Set α) : Set α :=
  π ⁻¹' (π '' A)

theorem subset_saturate (π : α → β) (A : Set α) :
    A ⊆ saturate π A := by
  intro a ha
  exact ⟨a, ha, rfl⟩

theorem saturate_idempotent (π : α → β) (A : Set α) :
    saturate π (saturate π A) = saturate π A := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, hzy⟩, hyx⟩
    exact ⟨z, hz, hzy.trans hyx⟩
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- After every product, discard the actual internal set, retaining labels only. -/
def hyperProd (op : α → α → α) (π : α → β)
    (U V : Set β) : Set β :=
  π '' setProd op (π ⁻¹' U) (π ⁻¹' V)

/-- The exact associativity criterion for the multivalued observational product.
    It identifies the two spurious saturation channels. -/
theorem hyper_assoc_iff_saturation (op : α → α → α) (π : α → β) :
    (∀ U V W : Set β,
       hyperProd op π (hyperProd op π U V) W =
         hyperProd op π U (hyperProd op π V W)) ↔
    (∀ U V W : Set β,
       π '' setProd op
         (saturate π (setProd op (π ⁻¹' U) (π ⁻¹' V))) (π ⁻¹' W) =
       π '' setProd op (π ⁻¹' U)
         (saturate π (setProd op (π ⁻¹' V) (π ⁻¹' W)))) := by
  rfl

/-- Product saturation is sufficient for hyper-associativity, not necessary. -/
theorem hyper_assoc_of_saturated_products (op : α → α → α)
    (π : α → β)
    (hassoc : ∀ a b c, op (op a b) c = op a (op b c))
    (hsat : ∀ U V : Set β,
      saturate π (setProd op (π ⁻¹' U) (π ⁻¹' V)) =
        setProd op (π ⁻¹' U) (π ⁻¹' V)) :
    ∀ U V W : Set β,
      hyperProd op π (hyperProd op π U V) W =
        hyperProd op π U (hyperProd op π V W) := by
  intro U V W
  change
    π '' setProd op
      (saturate π (setProd op (π ⁻¹' U) (π ⁻¹' V))) (π ⁻¹' W) =
    π '' setProd op (π ⁻¹' U)
      (saturate π (setProd op (π ⁻¹' V) (π ⁻¹' W)))
  rw [hsat U V, hsat V W, setProd_assoc op hassoc]

/-! ## Two finite certificates, using entirely computable Finset semantics. -/

/-- A finite exact-set product. -/
def finiteProd {γ : Type*} [DecidableEq γ]
    (op : γ → γ → γ) (A B : Finset γ) : Finset γ :=
  A.biUnion (fun x => B.image (op x))

def fiber {γ δ : Type*} [Fintype γ] [DecidableEq γ] [DecidableEq δ]
    (π : γ → δ) (q : δ) : Finset γ :=
  Finset.univ.filter (fun x => π x = q)

def finiteHyper {γ δ : Type*}
    [Fintype γ] [DecidableEq γ] [DecidableEq δ]
    (op : γ → γ → γ) (π : γ → δ)
    (p q : δ) : Finset δ :=
  (finiteProd op (fiber π p) (fiber π q)).image π

def finiteLift {δ : Type*} [DecidableEq δ]
    (h : δ → δ → Finset δ) (P Q : Finset δ) : Finset δ :=
  P.biUnion (fun p => Q.biUnion (fun q => h p q))

/-- A three-state nilpotent semigroup: 2·2=1 and all other products vanish. -/
def nilMul (x y : Fin 3) : Fin 3 :=
  if x = 2 ∧ y = 2 then 1 else 0

def nilObs (x : Fin 3) : Bool :=
  decide (x = 1)

theorem nilMul_assoc : ∀ x y z : Fin 3,
    nilMul (nilMul x y) z = nilMul x (nilMul y z) := by
  decide

def nilHyper (a b : Bool) : Finset Bool :=
  if a = false ∧ b = false then {false, true} else {false}

theorem nilHyper_correct (a b : Bool) :
    finiteHyper nilMul nilObs a b = nilHyper a b := by
  cases a <;> cases b <;> decide

theorem nilHyper_nonassociative :
    finiteLift nilHyper (nilHyper false false) ({true} : Finset Bool) ≠
      finiteLift nilHyper ({false} : Finset Bool) (nilHyper false true) := by
  decide

/-! ## A separate obstruction: associativity does NOT imply exactness. -/

/-- Addition in the five-element cyclic group. -/
def add5 (x y : Fin 5) : Fin 5 := x + y

def cyclicObs (x : Fin 5) : Fin 3 :=
  if x = 0 ∨ x = 1 then 0 else if x = 3 then 2 else 1

theorem add5_assoc : ∀ x y z : Fin 5,
    add5 (add5 x y) z = add5 x (add5 y z) := by
  decide

/-- The all-labels hyperoperation is associative on singleton inputs. -/
theorem cyclicHyper_associative_on_labels :
    ∀ a b c : Fin 3,
      finiteLift (finiteHyper add5 cyclicObs)
          (finiteHyper add5 cyclicObs a b) ({c} : Finset (Fin 3)) =
        finiteLift (finiteHyper add5 cyclicObs)
          ({a} : Finset (Fin 3)) (finiteHyper add5 cyclicObs b c) := by
  decide

/-- Concrete product of fibers B, B, C has exactly these output labels. -/
def cyclicExactTriple : Finset (Fin 3) :=
  (finiteProd add5
    (finiteProd add5 (fiber cyclicObs (1 : Fin 3))
      (fiber cyclicObs (1 : Fin 3)))
    (fiber cyclicObs (2 : Fin 3))).image cyclicObs

/-- Coarse multiplication first rounds each intermediate product up to fibers. -/
def cyclicApproxTriple : Finset (Fin 3) :=
  finiteLift (finiteHyper add5 cyclicObs)
    (finiteHyper add5 cyclicObs 1 1) ({2} : Finset (Fin 3))

theorem cyclic_exact_triple :
    cyclicExactTriple = ({0, 1} : Finset (Fin 3)) := by
  decide

theorem cyclic_approx_triple :
    cyclicApproxTriple = ({0, 1, 2} : Finset (Fin 3)) := by
  decide

theorem cyclic_spurious_observation :
    cyclicExactTriple ≠ cyclicApproxTriple := by
  decide

end VoidHyperCompletion
