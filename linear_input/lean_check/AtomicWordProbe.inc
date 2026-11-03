/-!
# Exact ONE additional identifying probe for ALL atomic words of <4,6,9>

Every actual atom is 4, 6 or 9. Hence each multiset of actual atoms
can be represented by unique generator multiplicities (r,s,t).
The previous theorem proves the final product together with s is
injective on generator multiplicities, so the same holds for all
irreducible multisets. The collision 4*9=6*6 shows zero extra probes
are insufficient. This strengthens the earlier two-candidate result.
-/

noncomputable section

namespace LinearInputAtomicWordProbe

open LinearInputGeneratedNonUnique
open LinearInputHalfFactorial
open LinearInputAtomicGeneratorClassification

def generatorWord (w : Counts) : Multiset G :=
  Multiset.replicate w.c4 four +
    Multiset.replicate w.c6 six +
    Multiset.replicate w.c9 nine

theorem generatorWord_product (w : Counts) :
    (generatorWord w).prod = valueInG w := by
  simp [generatorWord, valueInG, Multiset.prod_add]

theorem generatorWord_length (w : Counts) :
    (generatorWord w).card = length w := by
  simp [generatorWord, length]

theorem generatorWord_six_count (w : Counts) :
    (generatorWord w).count six = countSix w := by
  classical
  have h4 : four ≠ six := by
    intro h
    have hv := congrArg Subtype.val h
    norm_num [four, six] at hv
  have h9 : nine ≠ six := by
    intro h
    have hv := congrArg Subtype.val h
    norm_num [nine, six] at hv
  simp [generatorWord, countSix, Multiset.count_add,
    Multiset.count_replicate, h4, h9]

/-- The classification of actual atoms yields a generator-count code for
every finite atomic multiset, not merely for the words in an example. -/
theorem atomic_word_has_counts (w : Multiset G) :
    (∀ x ∈ w, Atomic x) →
      ∃ c : Counts, generatorWord c = w := by
  classical
  induction w using Multiset.induction_on with
  | empty =>
      intro _
      refine ⟨⟨0, 0, 0⟩, ?_⟩
      simp [generatorWord]
  | @cons a rest ih =>
      intro hw
      have ha : Atomic a := hw a (by simp)
      have hr : ∀ x ∈ rest, Atomic x := by
        intro x hx
        exact hw x (by simp [hx])
      obtain ⟨c, hc⟩ := ih hr
      rcases atom_is_generator a ha with h4 | h6 | h9
      · refine ⟨⟨c.c4 + 1, c.c6, c.c9⟩, ?_⟩
        rw [← hc, h4]
        simp [generatorWord, Multiset.replicate_succ]
      · refine ⟨⟨c.c4, c.c6 + 1, c.c9⟩, ?_⟩
        rw [← hc, h6]
        simp [generatorWord, Multiset.replicate_succ]
      · refine ⟨⟨c.c4, c.c6, c.c9 + 1⟩, ?_⟩
        rw [← hc, h9]
        simp [generatorWord, Multiset.replicate_succ]

/-- An observer counting the atomic factor 6 suffices to identify every
actual atomic word, once its final product is also known. -/
theorem product_and_six_identifies_all_atomic_words
    (u v : Multiset G)
    (hu : ∀ x ∈ u, Atomic x)
    (hv : ∀ x ∈ v, Atomic x)
    (hprod : u.prod = v.prod)
    (hsix : u.count six = v.count six) : u = v := by
  classical
  obtain ⟨a, ha⟩ := atomic_word_has_counts u hu
  obtain ⟨b, hb⟩ := atomic_word_has_counts v hv
  have hpA : (generatorWord a).prod = u.prod :=
    congrArg Multiset.prod ha
  have hpB : (generatorWord b).prod = v.prod :=
    congrArg Multiset.prod hb
  have hp : valueInG a = valueInG b := by
    simpa only [generatorWord_product] using
      hpA.trans (hprod.trans hpB.symm)
  have hsA : (generatorWord a).count six = u.count six :=
    congrArg (fun w : Multiset G => w.count six) ha
  have hsB : (generatorWord b).count six = v.count six :=
    congrArg (fun w : Multiset G => w.count six) hb
  have hs : countSix a = countSix b := by
    simpa only [generatorWord_six_count] using
      hsA.trans (hsix.trans hsB.symm)
  have hab : a = b :=
    actual_G_value_and_six_injective (Prod.ext hp hs)
  calc
    u = generatorWord a := ha.symm
    _ = generatorWord b := congrArg generatorWord hab
    _ = v := hb

/-- The old value-only observer is not enough even after restricting
to genuine atomic factors. -/
theorem product_alone_does_not_identify_all_atomic_words :
    ¬ ∀ u v : Multiset G,
      (∀ x ∈ u, Atomic x) →
      (∀ x ∈ v, Atomic x) →
      u.prod = v.prod → u = v := by
  intro h
  have h49 : ∀ x ∈ LinearInputGeneratedNonUnique.word49, Atomic x := by
    intro x hx
    simp only [LinearInputGeneratedNonUnique.word49, Multiset.mem_cons, Multiset.not_mem_zero,
      or_false] at hx
    rcases hx with rfl | rfl
    · exact four_atomic
    · exact nine_atomic
  have h66 : ∀ x ∈ LinearInputGeneratedNonUnique.word66, Atomic x := by
    intro x hx
    simp only [LinearInputGeneratedNonUnique.word66, Multiset.mem_cons, Multiset.not_mem_zero,
      or_false] at hx
    rcases hx with rfl | rfl <;> exact six_atomic
  exact words_distinct
    (h LinearInputGeneratedNonUnique.word49 LinearInputGeneratedNonUnique.word66 h49 h66 word_products_collide)

/-- In the one-element permitted family {countSix}, the minimum number
of additional observers needed to distinguish all actual atomic words
is exactly one (0 is insufficient, 1 is sufficient). -/
theorem exactly_one_extra_probe_for_all_atomic_words :
    (¬ ∀ u v : Multiset G,
      (∀ x ∈ u, Atomic x) →
      (∀ x ∈ v, Atomic x) →
      u.prod = v.prod → u = v) ∧
    (∀ u v : Multiset G,
      (∀ x ∈ u, Atomic x) →
      (∀ x ∈ v, Atomic x) →
      u.prod = v.prod → u.count six = v.count six → u = v) := by
  exact ⟨product_alone_does_not_identify_all_atomic_words,
    product_and_six_identifies_all_atomic_words⟩

end LinearInputAtomicWordProbe
