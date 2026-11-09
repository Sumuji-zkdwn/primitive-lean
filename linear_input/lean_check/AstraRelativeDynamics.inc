
/-!
# Relative energy along finite Kerr dynamics

For any finite skew spatial matrix, actual component derivatives imply an
exact relative-energy derivative. Skew cancellation leaves only the Kerr
constitutive remainder and an explicit residual in the comparison magnetic
equation. The resulting growth coefficient is independent of the number of
components. These results concern supplied differentiable finite trajectories;
they do not assert existence of a continuum PDE or convergence of projections.
-/

open scoped BigOperators

namespace KerrKoopman.RelativeDynamics

noncomputable section

open Riccati RelativeEnergy FiniteEnergy

variable {ι : Type*} [Fintype ι]

/-- Relative physical energy of one pair of electric and magnetic fields. -/
def relativeDensity (e h v j : ℝ) : ℝ :=
  electricGap e v + (j - h) ^ 2 / 2

/-- Summed relative energy for an arbitrary finite spatial discretization. -/
def relativeEnergy (E H V J : ι → ℝ) : ℝ :=
  ∑ i, relativeDensity (E i) (H i) (V i) (J i)

/-- The normalized constitutive remainder, without a small-amplitude cutoff. -/
def nonlinearRemainder (e v : ℝ) : ℝ :=
  (v - e) - (constitutive v - constitutive e) / (1 + e ^ 2)

theorem relativeDensity_nonneg (e h v j : ℝ) :
    0 ≤ relativeDensity e h v j := by
  unfold relativeDensity
  exact add_nonneg (electricGap_nonneg e v) (by positivity)

theorem relativeEnergy_nonneg (E H V J : ι → ℝ) :
    0 ≤ relativeEnergy E H V J := by
  exact Finset.sum_nonneg (fun i _ => relativeDensity_nonneg (E i) (H i) (V i) (J i))

theorem relativeDensity_eq_zero_iff (e h v j : ℝ) :
    relativeDensity e h v j = 0 ↔ v = e ∧ j = h := by
  constructor
  · intro hz
    have hg := electricGap_nonneg e v
    have hs := square_error_le_gap e v
    dsimp [relativeDensity] at hz
    constructor <;> nlinarith [sq_nonneg (v - e), sq_nonneg (j - h)]
  · rintro ⟨rfl, rfl⟩
    simp [relativeDensity, electricGap]

/-- Zero relative energy recovers both fields, without losing mode data. -/
theorem relativeEnergy_eq_zero_iff (E H V J : ι → ℝ) :
    relativeEnergy E H V J = 0 ↔ V = E ∧ J = H := by
  constructor
  · intro hz
    have hs := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => relativeDensity_nonneg (E i) (H i) (V i) (J i))).mp hz
    have hi : ∀ i, V i = E i ∧ J i = H i := fun i =>
      (relativeDensity_eq_zero_iff (E i) (H i) (V i) (J i)).mp
        (hs i (Finset.mem_univ i))
    exact ⟨funext (fun i => (hi i).1), funext (fun i => (hi i).2)⟩
  · rintro ⟨rfl, rfl⟩
    simp [relativeEnergy, relativeDensity, electricGap]

/-- Reconstruction of both physical field errors from the relative energy. -/
theorem squared_error_le_relativeEnergy (E H V J : ι → ℝ) :
    (∑ i, ((V i - E i) ^ 2 + (J i - H i) ^ 2)) ≤
      2 * relativeEnergy E H V J := by
  unfold relativeEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  dsimp [relativeDensity]
  linarith [square_error_le_gap (E i) (V i)]

/-- Differentiate the actual asymmetric constitutive energy gap. -/
theorem electricGap_hasDerivAt (e v : ℝ → ℝ) (e' v' t : ℝ)
    (he : HasDerivAt e e' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun z => electricGap (e z) (v z))
      ((v t - e t) * (1 + (v t) ^ 2) * v' -
        (constitutive (v t) - constitutive (e t)) * e') t := by
  have hve := density_hasDerivAt v (fun _ => 0) v' 0 t hv (hasDerivAt_const t 0)
  have hee := density_hasDerivAt e (fun _ => 0) e' 0 t he (hasDerivAt_const t 0)
  have hvd := constitutive_hasDerivAt v v' t hv
  have hed := constitutive_hasDerivAt e e' t he
  convert (hve.sub hee).sub (he.mul (hvd.sub hed)) using 1
  dsimp [electricGap, constitutive]
  ring

/-- Chain rule for the complete electric and magnetic relative density. -/
theorem relativeDensity_hasDerivAt (e h v j : ℝ → ℝ) (e' h' v' j' t : ℝ)
    (he : HasDerivAt e e' t) (hh : HasDerivAt h h' t)
    (hv : HasDerivAt v v' t) (hj : HasDerivAt j j' t) :
    HasDerivAt (fun z => relativeDensity (e z) (h z) (v z) (j z))
      ((v t - e t) * (1 + (v t) ^ 2) * v' -
        (constitutive (v t) - constitutive (e t)) * e' +
        (j t - h t) * (j' - h')) t := by
  convert (electricGap_hasDerivAt e v e' v' t he hv).add
    (((hj.sub hh).pow 2).div_const 2) using 1
  dsimp [relativeDensity]
  ring

theorem applyQ_sub (Q : ι → ι → ℝ) (u v : ι → ℝ) (i : ι) :
    applyQ Q (fun k => u k - v k) i = applyQ Q u i - applyQ Q v i := by
  simp only [applyQ, mul_sub, Finset.sum_sub_distrib]

/-- Exact scalar separation of the nonlinear remainder from spatial pairings. -/
theorem relativeRate_decomposition (e h v j qE qH qV qJ r : ℝ) :
    (v - e) * (1 + v ^ 2) * (-qJ / (1 + v ^ 2)) -
        (constitutive v - constitutive e) * (-qH / (1 + e ^ 2)) +
        (j - h) * ((-qV + r) - -qE) =
      -(v - e) * (qJ - qH) - (j - h) * (qV - qE) +
        (-qH) * nonlinearRemainder e v + (j - h) * r := by
  have he : 1 + e ^ 2 ≠ 0 := ne_of_gt (constitutive_denominator_pos e)
  have hv : 1 + v ^ 2 ≠ 0 := ne_of_gt (constitutive_denominator_pos v)
  unfold nonlinearRemainder
  field_simp
  ring

/-- Both wave directions are retained: the two cross pairings cancel by the
same skew matrix, without a simple-wave assumption. -/
theorem summed_relativeRate_eq (Q : ι → ι → ℝ)
    (hQ : ∀ i j, Q i j = -Q j i) (E H V J r : ι → ℝ) :
    (∑ i, ((V i - E i) * (1 + (V i) ^ 2) * electricRate Q V J i -
      (constitutive (V i) - constitutive (E i)) * electricRate Q E H i +
      (J i - H i) * ((magneticRate Q V i + r i) - magneticRate Q E i))) =
    ∑ i, ((-applyQ Q H i) * nonlinearRemainder (E i) (V i) +
      (J i - H i) * r i) := by
  have hp := skew_pairing Q hQ (fun i => V i - E i) (fun i => J i - H i)
  simp_rw [applyQ_sub] at hp
  simp only [electricRate, magneticRate, relativeRate_decomposition]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    neg_mul, Finset.sum_neg_distrib]
  linarith

/-- The exact time derivative follows from actual component equations. The
comparison magnetic equation may have a residual; no relative-energy
derivative or differential inequality is postulated. -/
theorem relativeEnergy_hasDerivAt (Q : ι → ι → ℝ)
    (hQ : ∀ i j, Q i j = -Q j i) (E H V J : ℝ → ι → ℝ)
    (r : ι → ℝ) (t : ℝ)
    (hE : ∀ i, HasDerivAt (fun z => E z i) (electricRate Q (E t) (H t) i) t)
    (hH : ∀ i, HasDerivAt (fun z => H z i) (magneticRate Q (E t) i) t)
    (hV : ∀ i, HasDerivAt (fun z => V z i) (electricRate Q (V t) (J t) i) t)
    (hJ : ∀ i, HasDerivAt (fun z => J z i) (magneticRate Q (V t) i + r i) t) :
    HasDerivAt (fun z => relativeEnergy (E z) (H z) (V z) (J z))
      (∑ i, ((-applyQ Q (H t) i) * nonlinearRemainder (E t i) (V t i) +
        (J t i - H t i) * r i)) t := by
  rw [← summed_relativeRate_eq Q hQ]
  exact HasDerivAt.fun_sum (fun i _ =>
    relativeDensity_hasDerivAt (fun z => E z i) (fun z => H z i)
      (fun z => V z i) (fun z => J z i) _ _ _ _ t (hE i) (hH i) (hV i) (hJ i))

/-- The pointwise nonlinear term uses the proved global constant three. -/
theorem nonlinear_term_le (e v d M : ℝ) (hM : 0 ≤ M) (hd : |d| ≤ M) :
    d * nonlinearRemainder e v ≤ 3 * M * electricGap e v := by
  calc
    d * nonlinearRemainder e v ≤ |d * nonlinearRemainder e v| := le_abs_self _
    _ = |d| * |nonlinearRemainder e v| := abs_mul _ _
    _ ≤ M * (3 * electricGap e v) :=
      mul_le_mul hd (constitutive_remainder_le_three_gap e v) (abs_nonneg _) hM
    _ = 3 * M * electricGap e v := by ring

/-- The magnetic residual is absorbed by the magnetic relative energy and
half its squared norm; the comparison amplitude need not be bounded. -/
theorem relativeRate_le (e h v j d r M : ℝ) (hM : 0 ≤ M) (hd : |d| ≤ M) :
    d * nonlinearRemainder e v + (j - h) * r ≤
      (3 * M + 1) * relativeDensity e h v j + r ^ 2 / 2 := by
  have hn := nonlinear_term_le e v d M hM hd
  have hy : (j - h) * r ≤ (j - h) ^ 2 / 2 + r ^ 2 / 2 := by
    nlinarith [sq_nonneg ((j - h) - r)]
  have hg := electricGap_nonneg e v
  have hm := mul_nonneg hM (sq_nonneg (j - h))
  dsimp [relativeDensity]
  nlinarith

/-- A dimension-independent rate bound for the full finite skew system. -/
theorem summed_relativeRate_le (Q : ι → ι → ℝ) (E H V J r : ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ i, |applyQ Q H i| ≤ M) :
    (∑ i, ((-applyQ Q H i) * nonlinearRemainder (E i) (V i) +
      (J i - H i) * r i)) ≤
    (3 * M + 1) * relativeEnergy E H V J + (∑ i, (r i) ^ 2) / 2 := by
  calc
    _ ≤ ∑ i, ((3 * M + 1) * relativeDensity (E i) (H i) (V i) (J i) +
        (r i) ^ 2 / 2) := by
      apply Finset.sum_le_sum
      intro i _
      exact relativeRate_le (E i) (H i) (V i) (J i) (-applyQ Q H i) (r i) M
        hM (by simpa only [abs_neg] using hbound i)
    _ = _ := by
      simp only [relativeEnergy, Finset.sum_add_distrib,
        Finset.mul_sum, Finset.sum_div]

/-- The actual physical-time derivative satisfies the rate estimate. This
connects the pointwise constitutive theorem to component evolution and
skew cancellation, rather than assuming an energy inequality. -/
theorem deriv_relativeEnergy_le (Q : ι → ι → ℝ)
    (hQ : ∀ i j, Q i j = -Q j i) (E H V J : ℝ → ι → ℝ)
    (r : ι → ℝ) (t M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ i, |applyQ Q (H t) i| ≤ M)
    (hE : ∀ i, HasDerivAt (fun z => E z i) (electricRate Q (E t) (H t) i) t)
    (hH : ∀ i, HasDerivAt (fun z => H z i) (magneticRate Q (E t) i) t)
    (hV : ∀ i, HasDerivAt (fun z => V z i) (electricRate Q (V t) (J t) i) t)
    (hJ : ∀ i, HasDerivAt (fun z => J z i) (magneticRate Q (V t) i + r i) t) :
    deriv (fun z => relativeEnergy (E z) (H z) (V z) (J z)) t ≤
      (3 * M + 1) * relativeEnergy (E t) (H t) (V t) (J t) +
        (∑ i, (r i) ^ 2) / 2 := by
  rw [(relativeEnergy_hasDerivAt Q hQ E H V J r t hE hH hV hJ).deriv]
  exact summed_relativeRate_le Q (E t) (H t) (V t) (J t) r M hM hbound

/-- A closed physical-time error formula derived from the component ODEs.
`ε` bounds half the squared residual on the interval. All spatial
dependence is retained; the estimate does not contain the component count. -/
theorem relativeEnergy_le_exp (Q : ι → ι → ℝ)
    (hQ : ∀ i j, Q i j = -Q j i) (E H V J r : ℝ → ι → ℝ)
    (a b t M ε : ℝ) (hM : 0 ≤ M) (ht : t ∈ Set.Icc a b)
    (hbound : ∀ z ∈ Set.Ico a b, ∀ i, |applyQ Q (H z) i| ≤ M)
    (hr : ∀ z ∈ Set.Ico a b, (∑ i, (r z i) ^ 2) / 2 ≤ ε)
    (hE : ∀ z ∈ Set.Icc a b, ∀ i,
      HasDerivAt (fun w => E w i) (electricRate Q (E z) (H z) i) z)
    (hH : ∀ z ∈ Set.Icc a b, ∀ i,
      HasDerivAt (fun w => H w i) (magneticRate Q (E z) i) z)
    (hV : ∀ z ∈ Set.Icc a b, ∀ i,
      HasDerivAt (fun w => V w i) (electricRate Q (V z) (J z) i) z)
    (hJ : ∀ z ∈ Set.Icc a b, ∀ i,
      HasDerivAt (fun w => J w i) (magneticRate Q (V z) i + r z i) z) :
    relativeEnergy (E t) (H t) (V t) (J t) ≤
      relativeEnergy (E a) (H a) (V a) (J a) * Real.exp ((3 * M + 1) * (t - a)) +
      ε / (3 * M + 1) * (Real.exp ((3 * M + 1) * (t - a)) - 1) := by
  let F : ℝ → ℝ := fun z => relativeEnergy (E z) (H z) (V z) (J z)
  let G : ℝ → ℝ := fun z =>
    ∑ i, ((-applyQ Q (H z) i) * nonlinearRemainder (E z i) (V z i) +
      (J z i - H z i) * r z i)
  have hd : ∀ z ∈ Set.Icc a b, HasDerivAt F (G z) z := by
    intro z hz
    exact relativeEnergy_hasDerivAt Q hQ E H V J (r z) z
      (hE z hz) (hH z hz) (hV z hz) (hJ z hz)
  have hc : ContinuousOn F (Set.Icc a b) :=
    fun z hz => (hd z hz).continuousAt.continuousWithinAt
  have hg : ∀ z ∈ Set.Ico a b, G z ≤ (3 * M + 1) * F z + ε := by
    intro z hz
    exact (summed_relativeRate_le Q (E z) (H z) (V z) (J z) (r z) M hM
      (hbound z hz)).trans (by dsimp [F]; linarith [hr z hz])
  have hgr := le_gronwallBound_of_liminf_deriv_right_le hc
    (fun z hz _ hs =>
      (hd z (Set.Ico_subset_Icc_self hz)).hasDerivWithinAt.liminf_right_slope_le hs)
    (le_refl (F a)) hg t ht
  have hK : 3 * M + 1 ≠ 0 := by linarith
  rw [gronwallBound_of_K_ne_0 hK] at hgr
  exact hgr

end

end KerrKoopman.RelativeDynamics
