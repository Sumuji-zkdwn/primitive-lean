import Mathlib

/-!
# Arbitrary-p two-layer Jordan normal form

For the transfer relation x^(p+1)=s*x^p-a, the first two shells of
polynomial observables (degree ≤2*p+1) have one 2-chain per residue
r=0,...,p. The companion coordinate operator below is a direct sum of
p+1 two-dimensional weighted nilpotent blocks.

The corresponding monomial formula is proved separately in
OrbitTraceFirstShell. This file proves the uniform coordinate-block
classification, not the full arbitrary-degree similarity theorem.
-/

namespace OrbitTrace

abbrev TwoLayer (p : ℕ) :=
  (Fin (p + 1) → ℚ) × (Fin (p + 1) → ℚ)

def twoLayerN (p : ℕ) (a : ℚ) (v : TwoLayer p) : TwoLayer p :=
  (fun i => -(((i.val + 1 : ℕ) : ℚ) * a) * v.2 i, fun _ => 0)

def twoLayerTop (p : ℕ) (i : Fin (p + 1)) : TwoLayer p :=
  (fun _ => 0, fun j => if j = i then 1 else 0)

theorem twoLayerN_square (p : ℕ) (a : ℚ) (v : TwoLayer p) :
    twoLayerN p a (twoLayerN p a v) =
      (fun _ => 0, fun _ => 0) := by
  apply Prod.ext
  · funext i
    simp [twoLayerN]
  · funext i
    simp [twoLayerN]

theorem twoLayerN_top_nonzero
    (p : ℕ) (a : ℚ) (ha : a ≠ 0) (i : Fin (p + 1)) :
    (twoLayerN p a (twoLayerTop p i)).1 i ≠ 0 := by
  have hi : (((i.val + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
  have hn : -(((i.val + 1 : ℕ) : ℚ) * a) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero hi ha)
  simpa [twoLayerN, twoLayerTop] using hn

theorem twoLayerN_surjective_onto_low
    (p : ℕ) (a : ℚ) (ha : a ≠ 0)
    (low : Fin (p + 1) → ℚ) :
    ∃ v : TwoLayer p,
      twoLayerN p a v = (low, fun _ => 0) := by
  let weight : Fin (p + 1) → ℚ :=
    fun i => -(((i.val + 1 : ℕ) : ℚ) * a)
  have hw (i : Fin (p + 1)) : weight i ≠ 0 := by
    dsimp [weight]
    have hi : (((i.val + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
    exact neg_ne_zero.mpr (mul_ne_zero hi ha)
  refine ⟨(fun _ => 0, fun i => low i / weight i), ?_⟩
  apply Prod.ext
  · funext i
    change weight i * (low i / weight i) = low i
    field_simp [hw i]
  · funext i
    rfl

theorem twoLayerN_kernel_is_low
    (p : ℕ) (a : ℚ) (ha : a ≠ 0)
    (v : TwoLayer p)
    (hz : twoLayerN p a v = (fun _ => 0, fun _ => 0)) :
    v.2 = fun _ => 0 := by
  funext i
  have hi : (((i.val + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
  have hw : -(((i.val + 1 : ℕ) : ℚ) * a) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero hi ha)
  have hcomp := congrArg (fun w : TwoLayer p => w.1 i) hz
  have hmul : (-(((i.val + 1 : ℕ) : ℚ) * a)) * v.2 i = 0 := by
    simpa only [twoLayerN] using hcomp
  exact (mul_eq_zero.mp hmul).resolve_left hw

#print axioms OrbitTrace.twoLayerN_square
#print axioms OrbitTrace.twoLayerN_top_nonzero
#print axioms OrbitTrace.twoLayerN_surjective_onto_low
#print axioms OrbitTrace.twoLayerN_kernel_is_low

end OrbitTrace
