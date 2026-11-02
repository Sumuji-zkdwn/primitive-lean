/-!
# WFS projective involution and a four-phase Fourier aliasing witness

The preceding TemporalSampling supplement proves that, for the zero-parameter
polynomial E map H(x,u)=(-u,x), even-step x observations are equivalent to
knowing x alone; full-step observations recover (x,u).

This additive supplement makes two *exact* further connections:
1. On positive intensity exp(x), the WFS p=2 even-step evolution is the
   Möbius map M(z)=-z/(1+2z), whose matrix is [[-1,0],[2,1]].
   It is a genuine involution on the interval z > -1/2.
2. The four x observations (x,-u,-x,u) have first Fourier coefficient
   (x+i*u)/2. Even-step sampling erases the u quadrature while preserving
   the x quadrature. This is a finite four-phase DFT example, not a
   universal Shannon-Nyquist theorem.

All WFS statements retain the strictly positive intensity domain.
-/

noncomputable section

namespace LinearInputWFSMobiusFourier

open LinearInputTemporalSampling
open LinearInputEWFSFuture
open LinearInputEWFSDual
open LinearInputFutureObservation

/-- A real fractional-linear map; the intended domain is 1+2*z>0. -/
def mobius (z : ℝ) : ℝ := -z / (1 + 2*z)

/-- WFS2 positive-intensity coordinates occupy z>-1/2. -/
theorem wfs2_range_positive (r : ℝ) (hr : 0 < r) :
    0 < 1 + 2 * wfs2 r := by
  have h : 1 + 2 * wfs2 r = r ^ 2 := by
    unfold wfs2
    ring
  rw [h]
  positivity

/-- Fundamental algebraic relation defining the projective involution. -/
theorem mobius_cross (z : ℝ) (hz : 1 + 2*z ≠ 0) :
    (1 + 2*z) * mobius z = -z := by
  unfold mobius
  field_simp [hz]

/-- The denominators of z and M(z) are multiplicative inverses. -/
theorem mobius_denominator_product (z : ℝ) (hz : 1 + 2*z ≠ 0) :
    (1 + 2*z) * (1 + 2*mobius z) = 1 := by
  have hm := mobius_cross z hz
  nlinarith

theorem mobius_preserves_domain (z : ℝ) (hz : 0 < 1 + 2*z) :
    0 < 1 + 2*mobius z := by
  have h := mobius_denominator_product z (ne_of_gt hz)
  nlinarith

/-- The Möbius map has order two on the positive WFS image. -/
theorem mobius_involutive (z : ℝ) (hz : 0 < 1 + 2*z) :
    mobius (mobius z) = z := by
  have h1 := mobius_cross z (ne_of_gt hz)
  have h2 := mobius_denominator_product z (ne_of_gt hz)
  have hpos := mobius_preserves_domain z hz
  have h3 := mobius_cross (mobius z) (ne_of_gt hpos)
  calc
    mobius (mobius z) =
        ((1 + 2*z) * (1 + 2*mobius z)) * mobius (mobius z) := by
      rw [h2]
      ring
    _ = (1 + 2*z) * ((1 + 2*mobius z) * mobius (mobius z)) := by ring
    _ = (1 + 2*z) * (-mobius z) := by rw [h3]
    _ = z := by linarith

/-- Reciprocal positive intensities correspond to the Möbius involution. -/
theorem mobius_wfs2_inverse (r : ℝ) (hr : r ≠ 0) :
    mobius (wfs2 r) = wfs2 r⁻¹ := by
  unfold mobius wfs2
  field_simp [hr]; ring

/-- The physical E quarter-rotation sampled every two updates acts as
the Möbius transformation on WFS2(exp(x)) observation coordinates. -/
theorem mobius_wfs2_exp_neg (x : ℝ) :
    mobius (wfs2 (Real.exp x)) = wfs2 (Real.exp (-x)) := by
  simpa only [Real.exp_neg] using
    mobius_wfs2_inverse (Real.exp x) (ne_of_gt (Real.exp_pos x))

theorem spin_two_mobius (z : ℝ × ℝ) :
    perceptualObservation (spinTwo z) = mobius (perceptualObservation z) := by
  rw [spinTwo_formula]
  change wfs2 (Real.exp (-z.1)) = mobius (wfs2 (Real.exp z.1))
  exact (mobius_wfs2_exp_neg z.1).symm

/-- The projective matrix of M has trace zero, determinant -1, and square I. -/
theorem mobius_matrix_involution :
    ((-1 : ℝ) * (-1) + 0 * 2 = 1) ∧
    ((-1 : ℝ) * 0 + 0 * 1 = 0) ∧
    ((2 : ℝ) * (-1) + 1 * 2 = 0) ∧
    ((2 : ℝ) * 0 + 1 * 1 = 1) := by
  norm_num

/-- Four successive x readings of the original E quarter-rotation. -/
def trace4 (z : ℝ × ℝ) (j : Fin 4) : ℝ :=
  observeX (spin^[j.val] z)

theorem trace4_values (z : ℝ × ℝ) :
    trace4 z 0 = z.1 ∧ trace4 z 1 = -z.2 ∧
    trace4 z 2 = -z.1 ∧ trace4 z 3 = z.2 := by
  simp [trace4, spin, H, observeX, Function.iterate_succ_apply']

/-- First 4-point Fourier mode, with the convention exp(-2*pi*i*j/4). -/
def fourier1 (z : ℝ × ℝ) : ℂ :=
  ((trace4 z 0 : ℂ) -
      Complex.I * (trace4 z 1 : ℂ) -
      (trace4 z 2 : ℂ) +
      Complex.I * (trace4 z 3 : ℂ)) / 4

theorem fourier1_formula (z : ℝ × ℝ) :
    fourier1 z = ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)) / 2 := by
  obtain ⟨h0,h1,h2,h3⟩ := trace4_values z
  unfold fourier1
  rw [h0, h1, h2, h3]
  push_cast
  ring

/-- The even samples of the four-step trace detect x, not the u quadrature. -/
theorem even_fourier_trace (z : ℝ × ℝ) :
    (trace4 z 0, trace4 z 2) = (z.1, -z.1) := by
  obtain ⟨h0, _, h2, _⟩ := trace4_values z
  rw [h0, h2]

/-- The hidden quarter-turn quadrature is recoverable from odd observations. -/
theorem odd_fourier_trace (z : ℝ × ℝ) :
    (trace4 z 1, trace4 z 3) = (-z.2, z.2) := by
  obtain ⟨_, h1, _, h3⟩ := trace4_values z
  rw [h1, h3]

/-- The first Fourier mode detects the hidden u even when the even
samples are identical: a finite, exact temporal aliasing witness. -/
theorem even_samples_erase_fourier_phase :
    (trace4 ((0 : ℝ), 0) 0, trace4 ((0 : ℝ), 0) 2) =
      (trace4 ((0 : ℝ), 1) 0, trace4 ((0 : ℝ), 1) 2) ∧
    fourier1 ((0 : ℝ), 0) ≠ fourier1 ((0 : ℝ), 1) := by
  constructor
  · rw [even_fourier_trace, even_fourier_trace]
  · rw [fourier1_formula, fourier1_formula]
    have hi : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    have hd : (Complex.I : ℂ) / 2 ≠ 0 := div_ne_zero hi (by norm_num)
    simpa using (Ne.symm hd)

end LinearInputWFSMobiusFourier
