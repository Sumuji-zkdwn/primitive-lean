import PrismAiryReflectance

/-!
# Oblique thin-film readout: geometry and a total-reflection lemma

The prism apex `A`, the glass-side incidence angle `alpha0`, and real
refracted angles `alpha1`, `alpha2` are separate quantities. Refracted angles
may be absent when Snell's radicand is negative. This file does not identify
the apex with the interface incidence angle.

For a planar stack, let `u = n0 sin(alpha0)` be the conserved tangential
index. The normal wave-number factor in medium `j` is
`qj = sqrt(nj^2-u^2)`. The numerical s/p Fresnel and transfer-matrix
calculation is independently checked by the adjacent Python program.

The formal result below is the algebraic TMM boundary case: a real incident
admittance, an evanescent (pure-imaginary) output admittance, and a film
characteristic matrix with real diagonal and pure-imaginary off-diagonal
entries imply unit reflected intensity. A coherent reflected phase can still
depend on film thickness. This conditional algebra does not prove that a
particular prism has this ray path or that a phase detector is installed.
-/

noncomputable section
namespace PrismObliqueTMM

open PrismAiryReflectance

/-- Geometry and ray angles are stored separately; `none` means no real
    refracted ray in that medium (an evanescent normal wave number). -/
structure RayGeometry where
  apexAngle : ℝ
  glassSideIncidence : ℝ
  filmRefraction : Option ℝ
  airRefraction : Option ℝ

/-- Conserved tangential index in Snell's law. `alpha0` is measured from the
    film-interface normal inside glass, never from the prism apex. -/
def tangentialIndex (alpha0 : ℝ) : ℝ := glassIndex * Real.sin alpha0

/-- The squared normal wave-number factor `n^2 - u^2`. -/
def snellRadicand (n u : ℝ) : ℝ := n^2 - u^2

/-- Above the critical condition `u > n`, Snell's law has no real cosine
    component in that medium. -/
theorem supercritical_radicand_negative (n u : ℝ)
    (hn : 0 < n) (hu : n < u) :
    snellRadicand n u < 0 := by
  unfold snellRadicand
  have hsum : 0 < u+n := by linarith
  have hprod : 0 < (u-n)*(u+n) := mul_pos (sub_pos.mpr hu) hsum
  nlinarith

theorem supercritical_has_no_real_refracted_cosine (n u : ℝ)
    (hn : 0 < n) (hu : n < u) :
    ¬ ∃ c : ℝ, 0 ≤ c ∧ snellRadicand n u = (n*c)^2 := by
  intro h
  rcases h with ⟨c, hc, hrad⟩
  have hneg := supercritical_radicand_negative n u hn hu
  unfold snellRadicand at hrad hneg
  nlinarith [sq_nonneg (n*c)]

/-- Real-coordinate representation of a characteristic matrix
    `[[a, i*b], [i*c, d]]` for a nonabsorbing film layer. -/
structure FilmMatrixPattern where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ

/-- Matrix multiplication preserves the real-diagonal / imaginary-off-
    diagonal pattern used by a stack of lossless planar layers. -/
def compose (x y : FilmMatrixPattern) : FilmMatrixPattern where
  a := x.a*y.a - x.b*y.c
  b := x.a*y.b + x.b*y.d
  c := x.c*y.a + x.d*y.c
  d := x.d*y.d - x.c*y.b

/-- The real and imaginary components of the transformed substrate term.
    The substrate admittance is `i*y2`; the incident admittance `y0` is real. -/
def inputReal (m : FilmMatrixPattern) (y0 y2 : ℝ) : ℝ :=
  y0 * (m.a - m.b*y2)

def inputImag (m : FilmMatrixPattern) (y2 : ℝ) : ℝ :=
  m.c + m.d*y2

/-- Reflected field intensity obtained from the TMM amplitude
    `(u-i*v)/(u+i*v)` in real/imaginary coordinates. -/
def reflectedIntensity (m : FilmMatrixPattern) (y0 y2 : ℝ) : ℝ :=
  let u := inputReal m y0 y2
  let v := inputImag m y2
  ((u^2-v^2)/(u^2+v^2))^2 + ((2*u*v)/(u^2+v^2))^2

theorem unit_intensity_of_conjugate_ratio (u v : ℝ)
    (h : u^2+v^2 ≠ 0) :
    ((u^2-v^2)/(u^2+v^2))^2 + ((2*u*v)/(u^2+v^2))^2 = 1 := by
  field_simp [h]
  ring

/-- Ideal lossless three-medium boundary case: if the output admittance is
    evanescent and nondegenerate, reflected intensity is independent of the
    film matrix entries and equals one. -/
theorem evanescent_output_reflectance_one (m : FilmMatrixPattern)
    (y0 y2 : ℝ)
    (hnondegenerate : (inputReal m y0 y2)^2 + (inputImag m y2)^2 ≠ 0) :
    reflectedIntensity m y0 y2 = 1 := by
  unfold reflectedIntensity
  exact unit_intensity_of_conjugate_ratio
    (inputReal m y0 y2) (inputImag m y2) hnondegenerate

end PrismObliqueTMM
