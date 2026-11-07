/-!
# Exact criterion for absence of hull inflation under a family of images

This is a general closure-operator statement, not an IUT p-adic theorem.
To apply it to Ind2, one must construct the actual induced maps and
verify the hypotheses for the genuine local holomorphic hull.

The equivalence separates two operations:
  individual images, and the closure of their union.
-/

noncomputable section

namespace LinearInputPilotHullStability

/-- The union of all images of a set under a family of operations. -/
def orbitUnion {A I : Type*} (ops : I → A → A) (S : Set A) : Set A :=
  ⋃ i, ops i '' S

/-- An identity choice embeds the original set into the orbit union. -/
theorem original_subset_orbit {A I : Type*}
    (ops : I → A → A) (S : Set A)
    (hid : ∃ i, ops i = id) : S ⊆ orbitUnion ops S := by
  obtain ⟨i, hi⟩ := hid
  intro x hx
  change x ∈ (⋃ j, ops j '' S)
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  simpa [hi] using hx

/-- Under the closure axioms, the hull over *all* images equals the
original hull exactly when each image stays in the original hull.
An identity operation is necessary for the reverse inclusion used here. -/
theorem orbit_hull_eq_iff_each_image_stable {A I : Type*}
    (ops : I → A → A) (S : Set A) (hull : Set A → Set A)
    (hmono : ∀ X Y, X ⊆ Y → hull X ⊆ hull Y)
    (hext : ∀ X, X ⊆ hull X)
    (hidempotent : ∀ X, hull (hull X) = hull X)
    (hid : ∃ i, ops i = id) :
    hull (orbitUnion ops S) = hull S ↔
      ∀ i, ops i '' S ⊆ hull S := by
  constructor
  · intro heq i x hx
    have ho : x ∈ orbitUnion ops S := by
      change x ∈ (⋃ j, ops j '' S)
      exact Set.mem_iUnion.mpr ⟨i, hx⟩
    have hcl : x ∈ hull (orbitUnion ops S) :=
      hext (orbitUnion ops S) ho
    rw [heq] at hcl
    exact hcl
  · intro hs
    have hu : orbitUnion ops S ⊆ hull S := by
      intro x hx
      change x ∈ (⋃ j, ops j '' S) at hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
      exact hs i hi
    apply Set.Subset.antisymm
    · calc
        hull (orbitUnion ops S) ⊆ hull (hull S) :=
          hmono _ _ hu
        _ = hull S := by rw [hidempotent S]
    · exact hmono _ _ (original_subset_orbit ops S hid)

/-- A single image escaping the original hull obstructs equality of the
two hull sets; strict volume inflation needs an additional measure fact. -/
theorem escaping_image_blocks_hull_equality {A I : Type*}
    (ops : I → A → A) (S : Set A) (hull : Set A → Set A)
    (hmono : ∀ X Y, X ⊆ Y → hull X ⊆ hull Y)
    (hext : ∀ X, X ⊆ hull X)
    (hidempotent : ∀ X, hull (hull X) = hull X)
    (hid : ∃ i, ops i = id)
    (hex : ∃ i x, x ∈ ops i '' S ∧ x ∉ hull S) :
    hull (orbitUnion ops S) ≠ hull S := by
  intro heq
  have hs := (orbit_hull_eq_iff_each_image_stable ops S hull
    hmono hext hidempotent hid).mp heq
  rcases hex with ⟨i, x, hx, hn⟩
  exact hn (hs i hx)

/-- If a volume is monotone under set inclusion, orbit-hull volume
cannot be smaller than the original hull volume. -/
theorem hull_orbit_volume_ge {A I : Type*}
    (ops : I → A → A) (S : Set A) (hull : Set A → Set A)
    (volume : Set A → ℝ)
    (hmono : ∀ X Y, X ⊆ Y → hull X ⊆ hull Y)
    (hvolmono : ∀ X Y, X ⊆ Y → volume X ≤ volume Y)
    (hid : ∃ i, ops i = id) :
    volume (hull S) ≤ volume (hull (orbitUnion ops S)) :=
  hvolmono _ _ (hmono _ _ (original_subset_orbit ops S hid))

/-- If every transformed image stays inside the old hull, a numerical
hull gap is exactly zero for any chosen volume functional. -/
theorem stable_images_give_zero_volume_gap {A I : Type*}
    (ops : I → A → A) (S : Set A) (hull : Set A → Set A)
    (volume : Set A → ℝ)
    (hmono : ∀ X Y, X ⊆ Y → hull X ⊆ hull Y)
    (hext : ∀ X, X ⊆ hull X)
    (hidempotent : ∀ X, hull (hull X) = hull X)
    (hid : ∃ i, ops i = id)
    (hs : ∀ i, ops i '' S ⊆ hull S) :
    volume (hull (orbitUnion ops S)) - volume (hull S) = 0 := by
  rw [(orbit_hull_eq_iff_each_image_stable ops S hull
    hmono hext hidempotent hid).mpr hs]
  ring

end LinearInputPilotHullStability
