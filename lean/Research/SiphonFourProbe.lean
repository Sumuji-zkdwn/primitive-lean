import Research.SiphonPolynomialE
import OrbitTrace

/-!
# Four tangent-distribution probability observations identify every real state

Maps are the existing polynomial shear E and linear turn L.
Reading p(z) = (1+9 z.1^4)⁻¹ is equivalent to reading z.1².
The global four-read result is proved from polynomial identities and positivity.
-/

namespace SiphonFourProbe

open Elastica.SiphonPolynomialE

private def B (u v : ℝ) : ℝ := (u + (v + u ^ 3) ^ 2) ^ 2
private def D (u v : ℝ) : ℝ := (v + (v - u + v ^ 3) ^ 2) ^ 2

private theorem sign_split (a b : ℝ) (h : a ^ 2 = b ^ 2) :
    b = a ∨ b = -a := by
  have hf : (b - a) * (b + a) = 0 := by nlinarith only [h]
  rcases mul_eq_zero.mp hf with hf | hf
  · left
    linarith
  · right
    linarith

private theorem B_both (u v : ℝ) :
    B u v - B (-u) (-v) = 4 * u * (v + u ^ 3) ^ 2 := by
  dsimp [B]
  ring

private theorem D_both (u v : ℝ) :
    D u v - D (-u) (-v) = 4 * v * (v - u + v ^ 3) ^ 2 := by
  dsimp [D]
  ring

private theorem B_u (u v : ℝ) :
    B u v - B (-u) v = 4 * u * (u ^ 6 + v ^ 2) * (1 + 2 * u ^ 2 * v) := by
  dsimp [B]
  ring

private theorem D_u (u v : ℝ) :
    D u v - D (-u) v =
      -8 * u * v * (1 + v ^ 2) * (u ^ 2 + v + (v + v ^ 3) ^ 2) := by
  dsimp [D]
  ring

private theorem B_v (u v : ℝ) :
    B u v - B u (-v) = 8 * u ^ 3 * v * (u ^ 6 + u + v ^ 2) := by
  dsimp [B]
  ring

private theorem D_v (u v : ℝ) :
    D u v - D u (-v) =
      -4 * v * (2 * u * (1 + v ^ 2) - 1) * (u ^ 2 + (v + v ^ 3) ^ 2) := by
  dsimp [D]
  ring

private theorem flip_v_impossible (u v : ℝ) (hv : v ≠ 0)
    (hb : B u v = B u (-v))
    (hd : D u v = D u (-v)) : False := by
  have hfact : (-4 : ℝ) * v * (2 * u * (1 + v ^ 2) - 1) *
      (u ^ 2 + (v + v ^ 3) ^ 2) = 0 := by
    calc
      _ = D u v - D u (-v) := (D_v u v).symm
      _ = 0 := sub_eq_zero.mpr hd
  have hvplus : v + v ^ 3 ≠ 0 := by
    have h : v + v ^ 3 = v * (1 + v ^ 2) := by ring
    rw [h]
    exact mul_ne_zero hv (by positivity)
  have hlast : 0 < u ^ 2 + (v + v ^ 3) ^ 2 := by
    have hsq : 0 < (v + v ^ 3) ^ 2 := sq_pos_of_ne_zero hvplus
    nlinarith [sq_nonneg u]
  have hbracket : 2 * u * (1 + v ^ 2) - 1 = 0 := by
    by_contra hne
    have hnon : (-4 : ℝ) * v * (2 * u * (1 + v ^ 2) - 1) *
        (u ^ 2 + (v + v ^ 3) ^ 2) ≠ 0 :=
      mul_ne_zero (mul_ne_zero
        (mul_ne_zero (by norm_num) hv) hne) (ne_of_gt hlast)
    exact hnon hfact
  have hu : 0 < u := by
    by_contra h
    have hn : u ≤ 0 := le_of_not_gt h
    have hm : u * (1 + v ^ 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hn (by positivity)
    nlinarith only [hm, hbracket]
  have hfactB : (8 : ℝ) * u ^ 3 * v * (u ^ 6 + u + v ^ 2) = 0 := by
    calc
      _ = B u v - B u (-v) := (B_v u v).symm
      _ = 0 := sub_eq_zero.mpr hb
  have hpositive : 0 < u ^ 6 + u + v ^ 2 := by positivity
  have hnon : (8 : ℝ) * u ^ 3 * v * (u ^ 6 + u + v ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero
      (by norm_num) (pow_ne_zero 3 (ne_of_gt hu))) hv) (ne_of_gt hpositive)
  exact hnon hfactB

private theorem flip_u_impossible (u v : ℝ) (hu : u ≠ 0)
    (hb : B u v = B (-u) v)
    (hd : D u v = D (-u) v) : False := by
  have hfact : (4 : ℝ) * u * (u ^ 6 + v ^ 2) * (1 + 2 * u ^ 2 * v) = 0 := by
    calc
      _ = B u v - B (-u) v := (B_u u v).symm
      _ = 0 := sub_eq_zero.mpr hb
  have hu2 : 0 < u ^ 2 := sq_pos_of_ne_zero hu
  have hu6 : 0 < u ^ 6 := by
    calc
      0 < (u ^ 2) ^ 3 := pow_pos hu2 _
      _ = u ^ 6 := by ring
  have hmid : 0 < u ^ 6 + v ^ 2 := by
    have hv2 : 0 ≤ v ^ 2 := sq_nonneg v
    linarith
  have hbracket : 1 + 2 * u ^ 2 * v = 0 := by
    by_contra hne
    have hnon : (4 : ℝ) * u * (u ^ 6 + v ^ 2) * (1 + 2 * u ^ 2 * v) ≠ 0 :=
      mul_ne_zero (mul_ne_zero
        (mul_ne_zero (by norm_num) hu) (ne_of_gt hmid)) hne
    exact hnon hfact
  have hv : v ≠ 0 := by
    intro hz
    simp [hz] at hbracket
  let a : ℝ := u ^ 2
  have ha : 0 < a := hu2
  have hmult : 2 * a * v = -1 := by
    dsimp [a]
    linarith only [hbracket]
  have hmul : 4 * a ^ 2 * v = -2 * a := by
    calc
      _ = (2 * a) * (2 * a * v) := by ring
      _ = -2 * a := by rw [hmult]; ring
  have hsquare : 4 * a ^ 2 * v ^ 2 = 1 := by
    calc
      _ = (2 * a * v) ^ 2 := by ring
      _ = 1 := by rw [hmult]; norm_num
  have hpoly : 0 < 4 * a ^ 3 - 2 * a + 1 := by
    have hsos : 4 * a ^ 3 - 2 * a + 1 =
        (2 * a - 1) ^ 2 + 2 * a * ((a - 1) ^ 2 + a ^ 2) := by ring
    rw [hsos]
    have hpos : 0 < 2 * a * ((a - 1) ^ 2 + a ^ 2) := by positivity
    have hsq : 0 ≤ (2 * a - 1) ^ 2 := sq_nonneg _
    linarith
  have hrel : 4 * a ^ 2 * (a + v + v ^ 2) = 4 * a ^ 3 - 2 * a + 1 := by
    calc
      _ = 4 * a ^ 3 + 4 * a ^ 2 * v + 4 * a ^ 2 * v ^ 2 := by ring
      _ = 4 * a ^ 3 - 2 * a + 1 := by rw [hmul, hsquare]; ring
  have hbase : 0 < a + v + v ^ 2 := by
    have hprod : 0 < 4 * a ^ 2 * (a + v + v ^ 2) := by
      rw [hrel]
      exact hpoly
    by_contra hn
    have hnNon : a + v + v ^ 2 ≤ 0 := le_of_not_gt hn
    have hcoeff : 0 ≤ 4 * a ^ 2 := by positivity
    have hnProd : 4 * a ^ 2 * (a + v + v ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hcoeff hnNon
    exact (not_le_of_gt hprod) hnProd
  have hbig : 0 < u ^ 2 + v + (v + v ^ 3) ^ 2 := by
    have h4 : 0 ≤ v ^ 4 := by positivity
    have h6 : 0 ≤ v ^ 6 := by positivity
    dsimp [a] at hbase
    nlinarith only [hbase, h4, h6]
  have hfactD : (-8 : ℝ) * u * v * (1 + v ^ 2) *
      (u ^ 2 + v + (v + v ^ 3) ^ 2) = 0 := by
    calc
      _ = D u v - D (-u) v := (D_u u v).symm
      _ = 0 := sub_eq_zero.mpr hd
  have hnon : (-8 : ℝ) * u * v * (1 + v ^ 2) *
      (u ^ 2 + v + (v + v ^ 3) ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (by norm_num) hu) hv)
      (by positivity)) (ne_of_gt hbig)
  exact hnon hfactD

private theorem flip_both_impossible (u v : ℝ) (hz : (u,v) ≠ (0,0))
    (hb : B u v = B (-u) (-v))
    (hd : D u v = D (-u) (-v)) : False := by
  have hfact : (4 : ℝ) * u * (v + u ^ 3) ^ 2 = 0 := by
    calc
      _ = B u v - B (-u) (-v) := (B_both u v).symm
      _ = 0 := sub_eq_zero.mpr hb
  have hfactD : (4 : ℝ) * v * (v - u + v ^ 3) ^ 2 = 0 := by
    calc
      _ = D u v - D (-u) (-v) := (D_both u v).symm
      _ = 0 := sub_eq_zero.mpr hd
  by_cases hu : u = 0
  · have hv : v ≠ 0 := by
      intro h
      apply hz
      simp [hu, h]
    have ht : v - u + v ^ 3 ≠ 0 := by
      have h : v - u + v ^ 3 = v * (1 + v ^ 2) := by
        rw [hu]
        ring
      rw [h]
      exact mul_ne_zero hv (by positivity)
    have hnon : (4 : ℝ) * v * (v - u + v ^ 3) ^ 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hv) (pow_ne_zero 2 ht)
    exact hnon hfactD
  · by_cases hr : v + u ^ 3 = 0
    · have hv : v = -u ^ 3 := by linarith
      have hvnon : v ≠ 0 := by
        rw [hv]
        exact neg_ne_zero.mpr (pow_ne_zero 3 hu)
      have ht : v - u + v ^ 3 ≠ 0 := by
        have hf : v - u + v ^ 3 = -u * (1 + u ^ 2 + u ^ 8) := by
          rw [hv]
          ring
        rw [hf]
        exact mul_ne_zero (neg_ne_zero.mpr hu) (by positivity)
      have hnon : (4 : ℝ) * v * (v - u + v ^ 3) ^ 2 ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) hvnon) (pow_ne_zero 2 ht)
      exact hnon hfactD
    · have hnon : (4 : ℝ) * u * (v + u ^ 3) ^ 2 ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) hu) (pow_ne_zero 2 hr)
      exact hnon hfact

private theorem four_square_core (u v x y : ℝ)
    (hu : u ^ 2 = x ^ 2)
    (hv : v ^ 2 = y ^ 2)
    (hb : B u v = B x y)
    (hd : D u v = D x y) : u = x ∧ v = y := by
  rcases sign_split u x hu with hx | hx
  · rcases sign_split v y hv with hy | hy
    · exact ⟨hx.symm, hy.symm⟩
    · by_cases hv0 : v = 0
      · refine ⟨hx.symm, ?_⟩
        rw [hy, hv0]
        ring
      · have hb' : B u v = B u (-v) := by simpa only [hx, hy] using hb
        have hd' : D u v = D u (-v) := by simpa only [hx, hy] using hd
        exact False.elim (flip_v_impossible u v hv0 hb' hd')
  · rcases sign_split v y hv with hy | hy
    · by_cases hu0 : u = 0
      · refine ⟨?_, hy.symm⟩
        rw [hx, hu0]
        ring
      · have hb' : B u v = B (-u) v := by simpa only [hx, hy] using hb
        have hd' : D u v = D (-u) v := by simpa only [hx, hy] using hd
        exact False.elim (flip_u_impossible u v hu0 hb' hd')
    · by_cases hz : (u,v) = (0,0)
      · have hu0 : u = 0 := congrArg Prod.fst hz
        have hv0 : v = 0 := congrArg Prod.snd hz
        constructor
        · rw [hx, hu0]
          ring
        · rw [hy, hv0]
          ring
      · have hb' : B u v = B (-u) (-v) := by simpa only [hx, hy] using hb
        have hd' : D u v = D (-u) (-v) := by simpa only [hx, hy] using hd
        exact False.elim (flip_both_impossible u v hz hb' hd')

def squareRead (z : ℝ × ℝ) : ℝ := z.1 ^ 2

/-- Four squared coordinate observations distinguish every real state. -/
theorem four_square_reads_injective (z w : ℝ × ℝ)
    (h0 : squareRead z = squareRead w)
    (hE : squareRead (E z) = squareRead (E w))
    (hL : squareRead (OrbitTrace.linearE z) =
          squareRead (OrbitTrace.linearE w))
    (hEL : squareRead (E (OrbitTrace.linearE z)) =
           squareRead (E (OrbitTrace.linearE w))) : z = w := by
  rcases z with ⟨u,v⟩
  rcases w with ⟨x,y⟩
  have hu : u ^ 2 = x ^ 2 := by simpa [squareRead] using h0
  have hv : v ^ 2 = y ^ 2 := by
    simpa [squareRead, OrbitTrace.linearE] using hL
  have hb : B u v = B x y := by
    simpa [squareRead, E, I, B] using hE
  have hd : D u v = D x y := by
    simpa [squareRead, E, I, D, OrbitTrace.linearE] using hEL
  obtain ⟨hu', hv'⟩ := four_square_core u v x y hu hv hb hd
  exact Prod.ext hu' hv'

/-- First probability weight in normalized squared tangent coordinate minors. -/
noncomputable def probabilityRead (z : ℝ × ℝ) : ℝ :=
  1 / (1 + 9 * z.1 ^ 4)

private theorem probability_implies_square (z w : ℝ × ℝ)
    (h : probabilityRead z = probabilityRead w) :
    squareRead z = squareRead w := by
  have ha : 1 + 9 * z.1 ^ 4 ≠ (0 : ℝ) := by positivity
  have hb : 1 + 9 * w.1 ^ 4 ≠ (0 : ℝ) := by positivity
  have hf : z.1 ^ 4 = w.1 ^ 4 := by
    unfold probabilityRead at h
    field_simp [ha, hb] at h
    nlinarith only [h]
  have hp : (z.1 ^ 2 - w.1 ^ 2) * (z.1 ^ 2 + w.1 ^ 2) = 0 := by
    nlinarith only [hf]
  rcases mul_eq_zero.mp hp with hdiff | hsum
  · dsimp [squareRead]
    linarith
  · dsimp [squareRead]
    nlinarith [sq_nonneg z.1, sq_nonneg w.1]

/-- Four probability-only readings identify every real state for the E,L maps. -/
theorem four_probability_reads_injective (z w : ℝ × ℝ)
    (h0 : probabilityRead z = probabilityRead w)
    (hE : probabilityRead (E z) = probabilityRead (E w))
    (hL : probabilityRead (OrbitTrace.linearE z) =
          probabilityRead (OrbitTrace.linearE w))
    (hEL : probabilityRead (E (OrbitTrace.linearE z)) =
           probabilityRead (E (OrbitTrace.linearE w))) : z = w := by
  exact four_square_reads_injective z w
    (probability_implies_square _ _ h0)
    (probability_implies_square _ _ hE)
    (probability_implies_square _ _ hL)
    (probability_implies_square _ _ hEL)

end SiphonFourProbe

#print axioms SiphonFourProbe.four_square_reads_injective
#print axioms SiphonFourProbe.four_probability_reads_injective
