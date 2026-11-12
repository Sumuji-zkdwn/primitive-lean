/-
Copyright (c) 2026 Sumuji-zkdwn.
SPDX-License-Identifier: Apache-2.0

Extended-complex-valued cross ratios. Unlike a totalized complex division,
this representation retains the infinite value of the projective ratio.
-/
import Research.MobiusProjectiveStructure

noncomputable section

namespace PrimitiveMobius

/-- The numerator and denominator of a four-point cross ratio form
a homogeneous pair, so its value may genuinely be infinity. -/
def crossRatioPair (p q r s : ℂ × ℂ) : ℂ × ℂ :=
  (bracket p r * bracket q s, bracket p s * bracket q r)

def crossRatioSphereHom (p q r s : ℂ × ℂ) : EComplex :=
  normalize (crossRatioPair p q r s)

def sphericalCrossRatio (p q r s : EComplex) : EComplex :=
  crossRatioSphereHom (pointLift p) (pointLift q) (pointLift r) (pointLift s)

/-- Normalization ignores nonzero common homogeneous scale. -/
theorem normalize_scale (k : ℂ) (hk : k ≠ 0) (p : ℂ × ℂ) :
    normalize (scale k p) = normalize p := by
  rcases p with ⟨x, y⟩
  by_cases hy : y = 0
  · simp [normalize, scale, hy]
  · have hky : k * y ≠ 0 := mul_ne_zero hk hy
    have hdiv : (k * x) / (k * y) = x / y := by
      field_simp [hk, hy]
      ring
    simp [normalize, scale, hy, hky, hdiv]

/-- Any four projective representatives can be rescaled independently. -/
theorem crossRatioPair_scale (a b c d : ℂ) (p q r s : ℂ × ℂ) :
    crossRatioPair (scale a p) (scale b q) (scale c r) (scale d s) =
      scale (a * b * c * d) (crossRatioPair p q r s) := by
  apply Prod.ext
  · change bracket (scale a p) (scale c r) *
      bracket (scale b q) (scale d s) =
      (a * b * c * d) * (bracket p r * bracket q s)
    rw [bracket_scale, bracket_scale]
    ring
  · change bracket (scale a p) (scale d s) *
      bracket (scale b q) (scale c r) =
      (a * b * c * d) * (bracket p s * bracket q r)
    rw [bracket_scale, bracket_scale]
    ring

/-- A matrix multiplies BOTH coordinates of the ratio by det(A)^2. -/
theorem crossRatioPair_hom (f : LinearFracTrans) (p q r s : ℂ × ℂ) :
    crossRatioPair (hom f p) (hom f q) (hom f r) (hom f s) =
      scale ((f.a * f.d - f.b * f.c) ^ 2) (crossRatioPair p q r s) := by
  apply Prod.ext
  · change bracket (hom f p) (hom f r) *
      bracket (hom f q) (hom f s) =
      (f.a * f.d - f.b * f.c) ^ 2 * (bracket p r * bracket q s)
    rw [bracket_hom, bracket_hom]
    ring
  · change bracket (hom f p) (hom f s) *
      bracket (hom f q) (hom f r) =
      (f.a * f.d - f.b * f.c) ^ 2 * (bracket p s * bracket q r)
    rw [bracket_hom, bracket_hom]
    ring

theorem crossRatioSphereHom_scale (a b c d : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (p q r s : ℂ × ℂ) :
    crossRatioSphereHom (scale a p) (scale b q)
      (scale c r) (scale d s) = crossRatioSphereHom p q r s := by
  dsimp [crossRatioSphereHom]
  rw [crossRatioPair_scale]
  apply normalize_scale
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb) hc) hd

theorem crossRatioSphereHom_invariant (f : LinearFracTrans)
    (p q r s : ℂ × ℂ) :
    crossRatioSphereHom (hom f p) (hom f q) (hom f r) (hom f s) =
      crossRatioSphereHom p q r s := by
  dsimp [crossRatioSphereHom]
  rw [crossRatioPair_hom]
  apply normalize_scale
  exact pow_ne_zero 2 f.determinant_ne_zero

/-- The usual projective-line-valued cross ratio is preserved by any
complex Möbius transformation, with infinity as a distinct value. -/
theorem sphericalCrossRatio_invariant (f : LinearFracTrans)
    (p q r s : EComplex) :
    sphericalCrossRatio (f p) (f q) (f r) (f s) =
      sphericalCrossRatio p q r s := by
  have hscale (z : EComplex) :
      ∃ k : ℂ, k ≠ 0 ∧
        pointLift (f z) = scale k (hom f (pointLift z)) := by
    rw [← normalize_hom_eq_action f z]
    exact pointLift_normalize_scale _ (hom_ne_zero f _ (pointLift_ne_zero z))
  obtain ⟨a, ha, hpa⟩ := hscale p
  obtain ⟨b, hb, hqb⟩ := hscale q
  obtain ⟨c, hc, hrc⟩ := hscale r
  obtain ⟨d, hd, hsd⟩ := hscale s
  dsimp [sphericalCrossRatio]
  rw [hpa, hqb, hrc, hsd]
  rw [crossRatioSphereHom_scale a b c d ha hb hc hd]
  exact crossRatioSphereHom_invariant f _ _ _ _

/-- At a zero denominator the value is truly the point at infinity. -/
theorem sphericalCrossRatio_pole :
    sphericalCrossRatio (some (0 : ℂ)) (some 1) (some 2) (some 0) =
      EComplex.infty := by
  norm_num [sphericalCrossRatio, crossRatioSphereHom, crossRatioPair,
    normalize, pointLift, bracket, EComplex.infty]

end PrimitiveMobius
