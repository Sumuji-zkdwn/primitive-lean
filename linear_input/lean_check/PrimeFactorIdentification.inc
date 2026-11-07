/-!
# Prime factorization as zero-extra-probe identification

This module specializes the general decomposition/observation framework
to positive natural numbers and Mathlib's PrimeMultiset. The multiplication
operation is fixed; changing the allowed class of factor words changes
whether final evaluation is injective.

Mathlib already supplies the fundamental arithmetic content through
PNat.factorMultiset and PrimeMultiset.factorMultiset_prod.
The results here connect those library theorems to the retained generic
rewrite and minimum-probe predicates. No new factorization algorithm or
complexity claim is made.
-/

noncomputable section

namespace LinearInputPrimeFactorIdentification

open LinearInputDecompositionIdentification

/-- Evaluating a multiset of primes uses the single commutative product. -/
def evaluatePrimeWord (u : PrimeMultiset) : ℕ+ := u.prod

/-- Canonical normal form of a strictly positive natural number. -/
def primeNormalForm (n : ℕ+) : PrimeMultiset := n.factorMultiset

/-- Every positive integer is reconstructed from its prime decomposition. -/
theorem evaluate_after_factor (n : ℕ+) :
    evaluatePrimeWord (primeNormalForm n) = n := by
  exact PNat.prod_factorMultiset n

/-- Factoring a product of prime atoms recovers exactly that multiset. -/
theorem factor_after_evaluate (u : PrimeMultiset) :
    primeNormalForm (evaluatePrimeWord u) = u := by
  exact PrimeMultiset.factorMultiset_prod u

/-- The product of a prime-only factor multiset uniquely identifies it. -/
theorem evaluatePrimeWord_injective :
    Function.Injective evaluatePrimeWord := by
  intro u v h
  calc
    u = primeNormalForm (evaluatePrimeWord u) := (factor_after_evaluate u).symm
    _ = primeNormalForm (evaluatePrimeWord v) := congrArg primeNormalForm h
    _ = v := factor_after_evaluate v

/-- Prime factorization identifies positive integers, including 1. -/
theorem primeNormalForm_injective :
    Function.Injective primeNormalForm := by
  intro n m h
  calc
    n = evaluatePrimeWord (primeNormalForm n) := (evaluate_after_factor n).symm
    _ = evaluatePrimeWord (primeNormalForm m) := congrArg evaluatePrimeWord h
    _ = m := evaluate_after_factor m

/-- The equivalence between positive integers and prime multiset normal forms. -/
def primeWordEquiv : PrimeMultiset ≃ ℕ+ where
  toFun := evaluatePrimeWord
  invFun := primeNormalForm
  left_inv := factor_after_evaluate
  right_inv := evaluate_after_factor

/-- Union of prime multisets corresponds to one commutative multiplication. -/
theorem evaluate_union (u v : PrimeMultiset) :
    evaluatePrimeWord (u + v) =
      evaluatePrimeWord u * evaluatePrimeWord v := by
  exact PrimeMultiset.prod_add u v

/-- Factoring a product corresponds to concatenating its atomic multisets. -/
theorem factor_product (n m : ℕ+) :
    primeNormalForm (n * m) = primeNormalForm n + primeNormalForm m := by
  exact PNat.factorMultiset_mul n m

/-- No evaluation-preserving rewrite changes an already normalized prime word. -/
theorem normalized_step_is_identity
    (R : PrimeMultiset → PrimeMultiset → Prop)
    (hpres : ∀ u v, R u v → evaluatePrimeWord u = evaluatePrimeWord v)
    {u v : PrimeMultiset} (h : R u v) : u = v := by
  exact evaluatePrimeWord_injective (hpres u v h)

/-- The terminal value is injective regardless of the rewrite relation:
prime-only words already have unique multiplicative values. -/
theorem prime_terminal_value_injective (R : PrimeMultiset → PrimeMultiset → Prop) :
    TerminalValueInjective R evaluatePrimeWord := by
  intro u v _ _ h
  exact evaluatePrimeWord_injective h

/-- Exactly zero additional probes are necessary to identify terminal
prime-only factor words, for any rewrite relation R. -/
theorem prime_zero_extra_probes
    (R : PrimeMultiset → PrimeMultiset → Prop) :
    IdentifiesWith R evaluatePrimeWord
      (fun (_ : Fin 0) (_ : PrimeMultiset) => PUnit.unit) ∅ := by
  exact (zero_extra_probes_iff R evaluatePrimeWord
    (fun (_ : Fin 0) (_ : PrimeMultiset) => PUnit.unit)).2
      (prime_terminal_value_injective R)

/-- Evaluation invariance and injectivity force the same terminal state
on any two finite derivations from a common starting prime word. -/
theorem prime_normal_form_unique
    (R : PrimeMultiset → PrimeMultiset → Prop)
    (hpres : ∀ u v, R u v → evaluatePrimeWord u = evaluatePrimeWord v)
    {x u v : PrimeMultiset}
    (hu : Steps R x u) (hv : Steps R x v)
    (htu : Terminal R u) (htv : Terminal R v) : u = v := by
  exact normal_forms_unique_of_value R evaluatePrimeWord hpres
    (prime_terminal_value_injective R) hu hv htu htv

/-- A multiset of natural-number prime atoms has unique total product,
expressed without the positive-integer wrapper in its statement. -/
theorem natural_prime_multiset_injective
    (u v : Multiset ℕ)
    (hu : ∀ p ∈ u, Nat.Prime p)
    (hv : ∀ p ∈ v, Nat.Prime p)
    (hprod : u.prod = v.prod) : u = v := by
  let U : PrimeMultiset := PrimeMultiset.ofNatMultiset u hu
  let V : PrimeMultiset := PrimeMultiset.ofNatMultiset v hv
  have hUV : U.prod = V.prod := by
    apply Subtype.ext
    change (U.prod : ℕ) = (V.prod : ℕ)
    calc
      (U.prod : ℕ) = u.prod := PrimeMultiset.prod_ofNatMultiset u hu
      _ = v.prod := hprod
      _ = (V.prod : ℕ) := (PrimeMultiset.prod_ofNatMultiset v hv).symm
  have h : U = V := evaluatePrimeWord_injective hUV
  calc
    u = U.toNatMultiset := (PrimeMultiset.to_ofNatMultiset u hu).symm
    _ = V.toNatMultiset := congrArg PrimeMultiset.toNatMultiset h
    _ = v := PrimeMultiset.to_ofNatMultiset v hv

/-- Multiplication alone need not identify a word built from composite
generators, even though it identifies prime-only words. -/
theorem composite_generators_not_identified :
    LinearInputDecompositionIdentification.evaluateFactors
      LinearInputDecompositionIdentification.factorsFourNine =
    LinearInputDecompositionIdentification.evaluateFactors
      LinearInputDecompositionIdentification.factorsSixSix ∧
    LinearInputDecompositionIdentification.factorsFourNine ≠
      LinearInputDecompositionIdentification.factorsSixSix := by
  exact ⟨LinearInputDecompositionIdentification.generator_collision.1.trans
    LinearInputDecompositionIdentification.generator_collision.2.1.symm,
    LinearInputDecompositionIdentification.generator_collision.2.2.1⟩

end LinearInputPrimeFactorIdentification
