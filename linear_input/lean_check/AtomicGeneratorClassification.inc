/-!
# Classification of all actual atoms in the generated submonoid <4,6,9>

Unlike a statement about syntactic generator words, this proves that
EVERY relative atom in the actual cancellative submonoid is one of the
three generators. A general closure-induction argument is enough:
an atomic product can have only a unit as one of its factors.

The generators are themselves atoms by the retained source.
No identification of an arbitrary atomic multiset with a multiplicity
triple is asserted by this module until an explicit coding theorem is added.
-/

noncomputable section

namespace LinearInputAtomicGeneratorClassification

open LinearInputGeneratedNonUnique

/-- A genuine relative atom cannot appear from multiplication of
two previously generated nonunit factors. -/
theorem atom_is_generator (x : G) (hx : Atomic x) :
    x = four ∨ x = six ∨ x = nine := by
  have key : ∀ n : ℕ, n ∈ generated →
      ∀ y : G, y.val = n → Atomic y → n ∈ generatorSet := by
    intro n hn
    refine Submonoid.closure_induction (s := generatorSet)
      (motive := fun n _ => ∀ y : G, y.val = n →
        Atomic y → n ∈ generatorSet) ?_ ?_ ?_ hn
    · intro n hn y hy hAtom
      exact hn
    · intro y hy hAtom
      exact False.elim (hAtom.1 hy)
    · intro a b ha hb hA hB y hy hAtom
      let ya : G := ⟨a, ha⟩
      let yb : G := ⟨b, hb⟩
      have hprod : ya * yb = y := by
        apply Subtype.ext
        exact hy.symm
      rcases hAtom.2 ya yb hprod with hleft | hright
      · change a = 1 at hleft
        subst a
        have hyb : y.val = b := by simpa using hy
        simpa using hB y hyb hAtom
      · change b = 1 at hright
        subst b
        have hya : y.val = a := by simpa using hy
        simpa using hA y hya hAtom
  have hs : x.val ∈ generatorSet :=
    key x.val x.property x rfl hx
  simp only [generatorSet, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hs
  rcases hs with h4 | h6 | h9
  · left
    apply Subtype.ext
    simpa [four] using h4
  · right
    left
    apply Subtype.ext
    simpa [six] using h6
  · right
    right
    apply Subtype.ext
    simpa [nine] using h9

/-- Complete atom list: all and only the original generators. -/
theorem atom_iff_three_generators (x : G) :
    Atomic x ↔ x = four ∨ x = six ∨ x = nine := by
  constructor
  · exact atom_is_generator x
  · intro h
    rcases h with rfl | rfl | rfl
    · exact four_atomic
    · exact six_atomic
    · exact nine_atomic

end LinearInputAtomicGeneratorClassification
