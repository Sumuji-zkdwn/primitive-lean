/-
Copyright (c) 2026 Sumuji-zkdwn.
SPDX-License-Identifier: Apache-2.0

New proofs relating the existing WFS fractional-linear involution to the
extended complex line, and a determinant-based projective cross ratio.
The imported EComplex source is attributed separately.
-/
import Research.EComplexThirdParty
import Mathlib.Tactic

noncomputable section

namespace PrimitiveMobius

/- The WFS matrix from WFSMobiusFourier.inc and WFSProjectiveSampling.inc. -/
def wfs : LinearFracTrans where
  a := -1
  b := 0
  c := 2
  d := 1
  determinant_ne_zero := by norm_num

theorem wfs_comp_self :
    LinearFracTrans.comp wfs wfs = LinearFracTrans.id := by
  ext <;> norm_num [LinearFracTrans.comp, LinearFracTrans.id, wfs]

/-- The observed WFS update is an involution on EVERY projective point. -/
theorem wfs_involutive (z : EComplex) :
    wfs (wfs z) = z := by
  calc
    wfs (wfs z) = (LinearFracTrans.comp wfs wfs) z :=
      (LinearFracTrans.comp_equivalent z wfs wfs).symm
    _ = (LinearFracTrans.id : LinearFracTrans) z := by rw [wfs_comp_self]
    _ = z := LinearFracTrans.id_apply z

/-- The former pole is a valid state of the extended complex plane. -/
theorem wfs_pole_to_infty :
    wfs (some (-(1 / 2 : ℂ))) = EComplex.infty := by
  norm_num [wfs, LinearFracTrans.apply, EComplex.infty]

/-- Infinity returns to the pole, rather than being a terminal state. -/
theorem wfs_infty_to_pole :
    wfs EComplex.infty = some (-(1 / 2 : ℂ)) := by
  norm_num [wfs, LinearFracTrans.apply, EComplex.infty]

theorem wfs_zero_fixed :
    wfs (some (0 : ℂ)) = some 0 := by
  norm_num [wfs, LinearFracTrans.apply]

/-- Homogeneous action of any invertible complex 2-by-2 matrix. -/
def hom (f : LinearFracTrans) (p : ℂ × ℂ) : ℂ × ℂ :=
  (f.a * p.1 + f.b * p.2, f.c * p.1 + f.d * p.2)

/-- The alternating bracket of two homogeneous vectors. -/
def bracket (p q : ℂ × ℂ) : ℂ := p.1 * q.2 - p.2 * q.1

theorem bracket_hom (f : LinearFracTrans) (p q : ℂ × ℂ) :
    bracket (hom f p) (hom f q) =
      (f.a * f.d - f.b * f.c) * bracket p q := by
  dsimp [bracket, hom]
  ring

private theorem cancel_common (k u v : ℂ) (hk : k ≠ 0) :
    (k * u) / (k * v) = u / v := by
  calc
    (k * u) / (k * v) = (k * k⁻¹) * (u / v) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = u / v := by simp [hk]

/-- Homogeneous cross ratio, including the case of a zero denominator.
Here complex zero is the deliberately totalized quotient convention. -/
def crossRatioHom (p q r s : ℂ × ℂ) : ℂ :=
  (bracket p r * bracket q s) / (bracket p s * bracket q r)

/-- For invertible matrices, the cross ratio is unchanged on homogenous pairs. -/
theorem crossRatioHom_invariant (f : LinearFracTrans) (p q r s : ℂ × ℂ) :
    crossRatioHom (hom f p) (hom f q) (hom f r) (hom f s) =
      crossRatioHom p q r s := by
  simp only [crossRatioHom, bracket_hom]
  let k : ℂ := f.a * f.d - f.b * f.c
  have hk : k ≠ 0 := f.determinant_ne_zero
  change ((k * bracket p r) * (k * bracket q s)) /
      ((k * bracket p s) * (k * bracket q r)) =
      (bracket p r * bracket q s) / (bracket p s * bracket q r)
  calc
    _ = ((k * k) * (bracket p r * bracket q s)) /
          ((k * k) * (bracket p s * bracket q r)) := by
            congr 1 <;> ring
    _ = _ := cancel_common (k * k)
      (bracket p r * bracket q s) (bracket p s * bracket q r)
      (mul_ne_zero hk hk)

/-- A canonical homogeneous representative for a finite point or infinity. -/
def pointLift : EComplex → ℂ × ℂ
  | none => (1, 0)
  | some z => (z, 1)

theorem pointLift_ne_zero (z : EComplex) :
    pointLift z ≠ (0, 0) := by
  cases z <;> norm_num [pointLift]

def extendedCrossRatio (p q r s : EComplex) : ℂ :=
  crossRatioHom (pointLift p) (pointLift q) (pointLift r) (pointLift s)

theorem extendedCrossRatio_finite (p q r s : ℂ) :
    extendedCrossRatio (some p) (some q) (some r) (some s) =
      ((p - r) * (q - s)) / ((p - s) * (q - r)) := by
  simp [extendedCrossRatio, crossRatioHom, pointLift, bracket]

/-- Distinct triples determine the projective action (not raw coefficients). -/
theorem triple_determines_action (f g : LinearFracTrans) (p q r : EComplex)
    (hd : p ≠ q ∧ q ≠ r ∧ r ≠ p)
    (hp : f p = g p) (hq : f q = g q) (hr : f r = g r) :
    ∀ z : EComplex, f z = g z := by
  exact LinearFracTrans.lft_uniqueness f g p q r hd hp hq hr

/-- Two triples of mutually distinct points have an LFT between them. -/
theorem triple_transport (p q r p' q' r' : EComplex)
    (hd : p ≠ q ∧ q ≠ r ∧ r ≠ p)
    (hd' : p' ≠ q' ∧ q' ≠ r' ∧ r' ≠ p') :
    ∃ f : LinearFracTrans,
      f p = p' ∧ f q = q' ∧ f r = r' := by
  exact LinearFracTrans.exist_LFT_mapping_three_point p q r p' q' r' hd hd'

/-- Functional equality is exactly coefficient proportionality. -/
theorem same_projective_map_iff_proportional (f g : LinearFracTrans) :
    (∀ z : EComplex, f z = g z) ↔ f.Proportional g := by
  exact LinearFracTrans.funEq_iff_proportional f g

/-- The WFS homogeneous operator agrees with the pre-existing real lift. -/
theorem hom_wfs (p : ℂ × ℂ) :
    hom wfs p = (-p.1, 2 * p.1 + p.2) := by
  simp [hom, wfs]

end PrimitiveMobius
