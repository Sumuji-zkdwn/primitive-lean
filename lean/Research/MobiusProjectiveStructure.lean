/-
Copyright (c) 2026 Sumuji-zkdwn.
SPDX-License-Identifier: Apache-2.0

Canonical projective coordinates, PGL action as a subgroup of permutations,
and genuine extended cross-ratio invariance.
-/
import Research.MobiusProjectiveCompletion
import Mathlib.Algebra.Group.Action.End

noncomputable section

namespace PrimitiveMobius

private theorem cancel_common (k u v : ℂ) (hk : k ≠ 0) :
    (k * u) / (k * v) = u / v := by
  calc
    (k * u) / (k * v) = (k * k⁻¹) * (u / v) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = u / v := by simp [hk]

/-- The Möbius group realized faithfully as permutations of the sphere. -/
def actionHom : LinearFracTrans →* Equiv.Perm EComplex :=
  MulAction.toPermHom LinearFracTrans EComplex

/-- A group model for PGL(2,C), namely the image of the invertible
2x2 complex matrices in permutations of the projective line. -/
def projectiveMobiusGroup : Subgroup (Equiv.Perm EComplex) :=
  actionHom.range

/-- Two matrices induce the same projective permutation iff they differ
by a nonzero scalar. -/
theorem actionHom_eq_iff_proportional (f g : LinearFracTrans) :
    actionHom f = actionHom g ↔ f.Proportional g := by
  constructor
  · intro h
    apply (LinearFracTrans.funEq_iff_proportional f g).mp
    intro z
    have hz := congrArg (fun e : Equiv.Perm EComplex => e z) h
    change f z = g z at hz
    exact hz
  · intro h
    apply Equiv.ext
    intro z
    change f z = g z
    exact (LinearFracTrans.proportional2FunEq f g h) z

/-- Scaling a nonzero homogeneous coordinate pair represents the same point. -/
def scale (k : ℂ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (k * p.1, k * p.2)

theorem bracket_scale (a b : ℂ) (p q : ℂ × ℂ) :
    bracket (scale a p) (scale b q) = (a * b) * bracket p q := by
  dsimp [bracket, scale]
  ring

/-- Projective cross ratios do not depend on nonzero scalings of the
four homogeneous representatives, including an infinite point. -/
theorem crossRatioHom_scale (a b c d : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (p q r s : ℂ × ℂ) :
    crossRatioHom (scale a p) (scale b q) (scale c r) (scale d s) =
      crossRatioHom p q r s := by
  simp only [crossRatioHom, bracket_scale]
  let k : ℂ := a * b * c * d
  have hk : k ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb) hc) hd
  change (((a * c) * bracket p r) * ((b * d) * bracket q s)) /
    (((a * d) * bracket p s) * ((b * c) * bracket q r)) =
    (bracket p r * bracket q s) / (bracket p s * bracket q r)
  calc
    _ = (k * (bracket p r * bracket q s)) /
        (k * (bracket p s * bracket q r)) := by
          congr 1 <;> ring
    _ = _ := cancel_common k _ _ hk

/-- The coordinate point [X:Y] is represented by X/Y if Y is nonzero,
and infinity when Y is zero. -/
def normalize (p : ℂ × ℂ) : EComplex :=
  if p.2 = 0 then none else some (p.1 / p.2)

/-- Normalization and the canonical affine/infinite lift are inverse. -/
theorem normalize_pointLift (z : EComplex) :
    normalize (pointLift z) = z := by
  cases z <;> simp [normalize, pointLift]

/-- Every nonzero pair is a nonzero scalar multiple of its normalized lift. -/
theorem pointLift_normalize_scale (p : ℂ × ℂ) (hp : p ≠ (0, 0)) :
    ∃ k : ℂ, k ≠ 0 ∧ pointLift (normalize p) = scale k p := by
  rcases p with ⟨x, y⟩
  by_cases hy : y = 0
  · have hx : x ≠ 0 := by
      intro hx
      apply hp
      simp [hx, hy]
    refine ⟨x⁻¹, inv_ne_zero hx, ?_⟩
    simp [normalize, pointLift, scale, hy, hx]
  · refine ⟨y⁻¹, inv_ne_zero hy, ?_⟩
    simp [normalize, pointLift, scale, hy, div_eq_mul_inv, mul_comm]

/-- Invertible matrix action never sends a nonzero vector to zero. -/
theorem hom_ne_zero (f : LinearFracTrans) (p : ℂ × ℂ)
    (hp : p ≠ (0, 0)) : hom f p ≠ (0, 0) := by
  intro hz
  have h1 : f.a * p.1 + f.b * p.2 = 0 := by
    have h := congrArg Prod.fst hz
    simpa [hom] using h
  have h2 : f.c * p.1 + f.d * p.2 = 0 := by
    have h := congrArg Prod.snd hz
    simpa [hom] using h
  have hx : (f.a * f.d - f.b * f.c) * p.1 = 0 := by
    calc
      _ = f.d * (f.a * p.1 + f.b * p.2) -
          f.b * (f.c * p.1 + f.d * p.2) := by ring
      _ = 0 := by rw [h1, h2]; ring
  have hy : (f.a * f.d - f.b * f.c) * p.2 = 0 := by
    calc
      _ = f.a * (f.c * p.1 + f.d * p.2) -
          f.c * (f.a * p.1 + f.b * p.2) := by ring
      _ = 0 := by rw [h1, h2]; ring
  apply hp
  apply Prod.ext
  · exact (mul_eq_zero.mp hx).resolve_left f.determinant_ne_zero
  · exact (mul_eq_zero.mp hy).resolve_left f.determinant_ne_zero

/-- Homogeneous matrix action agrees with the extended complex LFT action. -/
theorem normalize_hom_eq_action (f : LinearFracTrans) (z : EComplex) :
    normalize (hom f (pointLift z)) = f z := by
  cases z with
  | none =>
      simp [normalize, pointLift, hom, LinearFracTrans.apply]
  | some z =>
      by_cases hc : f.c = 0
      · have hd : f.d ≠ 0 :=
          (LinearFracTrans.a_d_nonzero_of_c_zero f.determinant_ne_zero hc).2
        simp [normalize, pointLift, hom, LinearFracTrans.apply,
          hc, hd, div_eq_mul_inv, add_mul, mul_comm, mul_assoc]
      · have hpole : (f.c * z + f.d = 0) ↔ z = -f.d / f.c := by
          constructor
          · intro h
            apply (eq_div_iff hc).mpr
            linear_combination h
          · intro h
            rw [h]
            field_simp [hc]
            ring
        by_cases hden : f.c * z + f.d = 0
        · have hzp : z = -f.d / f.c := hpole.mp hden
          have hden' : f.c * (-f.d / f.c) + f.d = 0 := by
            simpa [hzp] using hden
          simp [normalize, pointLift, hom, LinearFracTrans.apply, hc,
            hzp, hden']
        · have hzn : z ≠ -f.d / f.c := fun h => hden (hpole.mpr h)
          simp [normalize, pointLift, hom, LinearFracTrans.apply, hc,
            hden, hzn]

/-- Complete extended-sphere cross-ratio invariance, not just a formula
on unnormalized pairs. Infinity is a first-class point. -/
theorem extendedCrossRatio_invariant (f : LinearFracTrans)
    (p q r s : EComplex) :
    extendedCrossRatio (f p) (f q) (f r) (f s) =
      extendedCrossRatio p q r s := by
  have hscale (z : EComplex) :
      ∃ k : ℂ, k ≠ 0 ∧
        pointLift (f z) = scale k (hom f (pointLift z)) := by
    rw [← normalize_hom_eq_action f z]
    exact pointLift_normalize_scale _ (hom_ne_zero f _ (pointLift_ne_zero z))
  obtain ⟨a, ha, hpa⟩ := hscale p
  obtain ⟨b, hb, hqb⟩ := hscale q
  obtain ⟨c, hc, hrc⟩ := hscale r
  obtain ⟨d, hd, hsd⟩ := hscale s
  simp only [extendedCrossRatio, hpa, hqb, hrc, hsd]
  rw [crossRatioHom_scale a b c d ha hb hc hd, crossRatioHom_invariant]

end PrimitiveMobius
