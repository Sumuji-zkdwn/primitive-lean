import OrbitTraceRankFormula

/-!
# The constructive Jordan chain basis of the canonical transfer deviation

Section 11 of `docs/research/2026-11-04-orbit-trace-integrals.md` describes, as a
hand proof, an explicit basis of `V_d = Q[X]_{≤ d}` adapted to
`N = canonicalDelta p a` (`a ≠ 0`, `q = p + 1`):

  `v_{r,j} = N^{ℓ_r - 1 - j} (X^{t_r})`,  `ℓ_r = ⌊(d - r)/q⌋ + 1`,  `t_r = r + (ℓ_r - 1) q`,

for residues `r ≤ min(p, d)` and `0 ≤ j < ℓ_r`, with `N v_{r,0} = 0` and
`N v_{r,j} = v_{r,j-1}`. This file proves it, using the `ExactShift` property of
`OrbitTraceRankFormula.lean`.

* `chainVec_natDegree`: `v_{r,j}` is nonzero of degree exactly `r + j q`.
* `chainVec_bottom`, `chainVec_succ`: `N v_{r,0} = 0`, `N v_{r,j+1} = v_{r,j}`.
* `jordanSequence`: placing `v_{k mod q, k div q}` in degree `k ≤ d` gives a
  polynomial sequence; hence the chain vectors are linearly independent
  (`jordan_linearIndependent`) and span exactly `V_d` (`jordan_span`).

Together these are the Jordan decomposition of `N` on `V_d` into `min(p, d) + 1`
chains of lengths `ℓ_r`, in the explicit basis of the note.
-/

namespace OrbitTrace

open Polynomial

/-- Top index `M_r = ⌊(d - r)/(p+1)⌋ = ℓ_r - 1` of the chain with residue `r`. -/
def chainTop (p d r : ℕ) : ℕ := (d - r) / (p + 1)

/-- The chain vector `v_{r,j} = N^{M_r - j} (X^{r + M_r (p+1)})`. -/
noncomputable def chainVec (p : ℕ) (a : ℚ) (d r j : ℕ) : ℚ[X] :=
  (canonicalDelta p a ^ (chainTop p d r - j)) (X ^ (r + chainTop p d r * (p + 1)))

/-- Degree `k ≤ d` gets `v_{k mod q, k div q}`; higher degrees are padded by `X^k`. -/
noncomputable def jordanElem (p : ℕ) (a : ℚ) (d k : ℕ) : ℚ[X] :=
  if k ≤ d then chainVec p a d (k % (p + 1)) (k / (p + 1)) else X ^ k

theorem pow_succ_apply_left (f : Module.End ℚ ℚ[X]) (n : ℕ) (x : ℚ[X]) :
    (f ^ (n + 1)) x = f ((f ^ n) x) := by
  rw [pow_succ']
  rfl

variable {p : ℕ} {a : ℚ} {d : ℕ}

/-- The chain length is `ℓ_r = chainTop + 1`, i.e. `chainLength` of `OrbitTraceJordanIndex`. -/
theorem chainTop_succ_eq_chainLength {r : ℕ} (hr : r ≤ d) :
    chainTop p d r + 1 = chainLength p d r := by
  simp [chainTop, chainLength, hr]

theorem chainTop_mul_le (r : ℕ) : chainTop p d r * (p + 1) ≤ d - r :=
  Nat.div_mul_le_self _ _

/-- `v_{r,j}` is nonzero with degree exactly `r + j (p+1)`. -/
theorem chainVec_natDegree (ha : a ≠ 0) {r j : ℕ} (hj : j ≤ chainTop p d r) :
    chainVec p a d r j ≠ 0 ∧ (chainVec p a d r j).natDegree = r + j * (p + 1) := by
  have hT := (canonicalDelta_exactShift p a ha).pow (chainTop p d r - j)
  have hX : (X : ℚ[X]) ^ (r + chainTop p d r * (p + 1)) ≠ 0 := pow_ne_zero _ X_ne_zero
  have hle : (chainTop p d r - j) * (p + 1) ≤ r + chainTop p d r * (p + 1) := by
    rw [Nat.sub_mul]
    omega
  obtain ⟨hne, hdeg⟩ := (hT _).2 hX (by rw [natDegree_X_pow]; exact hle)
  refine ⟨hne, ?_⟩
  rw [chainVec, hdeg, natDegree_X_pow, Nat.sub_mul]
  have : j * (p + 1) ≤ chainTop p d r * (p + 1) := Nat.mul_le_mul_right _ hj
  omega

/-- Bottom of each chain: `N v_{r,0} = 0` (for a genuine residue `r < p + 1`). -/
theorem chainVec_bottom (ha : a ≠ 0) {r : ℕ} (hr : r < p + 1) :
    canonicalDelta p a (chainVec p a d r 0) = 0 := by
  rw [chainVec, Nat.sub_zero, ← pow_succ_apply_left]
  have hT := (canonicalDelta_exactShift p a ha).pow (chainTop p d r + 1)
  apply (hT _).1
  rw [natDegree_X_pow, Nat.succ_mul]
  omega

/-- Chain step: `N v_{r,j+1} = v_{r,j}`. -/
theorem chainVec_succ {r j : ℕ} (hj : j + 1 ≤ chainTop p d r) :
    canonicalDelta p a (chainVec p a d r (j + 1)) = chainVec p a d r j := by
  rw [chainVec, chainVec, ← pow_succ_apply_left]
  congr 2
  omega

/-! ## The chain vectors as a polynomial sequence -/

theorem div_le_chainTop {k : ℕ} (hk : k ≤ d) : k / (p + 1) ≤ chainTop p d (k % (p + 1)) := by
  rw [chainTop, Nat.le_div_iff_mul_le (by omega : 0 < p + 1)]
  have := Nat.mod_add_div' k (p + 1)
  omega

theorem jordanElem_natDegree (ha : a ≠ 0) (k : ℕ) :
    jordanElem p a d k ≠ 0 ∧ (jordanElem p a d k).natDegree = k := by
  unfold jordanElem
  split_ifs with hk
  · obtain ⟨hne, hdeg⟩ := chainVec_natDegree (p := p) (a := a) (d := d) ha (div_le_chainTop hk)
    exact ⟨hne, hdeg.trans (Nat.mod_add_div' k (p + 1))⟩
  · exact ⟨pow_ne_zero _ X_ne_zero, natDegree_X_pow k⟩

/-- The chain vectors (padded above `d`) form a polynomial sequence: degree `k` in slot `k`. -/
noncomputable def jordanSequence (ha : a ≠ 0) : Polynomial.Sequence ℚ where
  elems' := jordanElem p a d
  degree_eq' k := by
    obtain ⟨hne, hdeg⟩ := jordanElem_natDegree (p := p) (d := d) ha k
    rw [degree_eq_natDegree hne, hdeg]

theorem jordanSequence_apply (ha : a ≠ 0) (k : ℕ) :
    jordanSequence (p := p) (d := d) ha k = jordanElem p a d k := rfl

/-- **Linear independence** of the chain vectors (with the padding above `d`). -/
theorem jordan_linearIndependent (ha : a ≠ 0) :
    LinearIndependent ℚ (jordanElem p a d) :=
  (jordanSequence (p := p) (d := d) ha).linearIndependent

/-- **Spanning**: the chain vectors of degree `≤ d` span exactly `V_d`. -/
theorem jordan_span (ha : a ≠ 0) :
    Submodule.span ℚ (jordanElem p a d '' Set.Iio (d + 1)) = degreeLT ℚ (d + 1) :=
  (jordanSequence (p := p) (d := d) ha).span_degreeLT fun i _ =>
    isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr
      (jordanElem_natDegree (p := p) (d := d) ha i).1)

/-- In the slot picture: `N` sends the basis vector of degree `k ≤ d` to the one of degree
`k - (p+1)` when `k ≥ p + 1`, and to `0` otherwise. -/
theorem jordanElem_delta (ha : a ≠ 0) {k : ℕ} (hk : k ≤ d) :
    canonicalDelta p a (jordanElem p a d k) =
      if p + 1 ≤ k then jordanElem p a d (k - (p + 1)) else 0 := by
  split_ifs with hq
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + (p + 1) := ⟨k - (p + 1), by omega⟩
    have hmod : (m + (p + 1)) % (p + 1) = m % (p + 1) := Nat.add_mod_right _ _
    have hdiv : (m + (p + 1)) / (p + 1) = m / (p + 1) + 1 :=
      Nat.add_div_right _ (by omega)
    have htop := div_le_chainTop (p := p) (d := d) hk
    rw [hmod, hdiv] at htop
    have hm : m ≤ d := by omega
    unfold jordanElem
    simp only [hk, hm, Nat.add_sub_cancel, ↓reduceIte]
    rw [hmod, hdiv]
    exact chainVec_succ htop
  · have hr : k % (p + 1) < p + 1 := Nat.mod_lt _ (by omega)
    have hdiv : k / (p + 1) = 0 := Nat.div_eq_of_lt (by omega)
    unfold jordanElem
    simp only [hk, ↓reduceIte]
    rw [hdiv]
    exact chainVec_bottom ha hr

#print axioms OrbitTrace.chainVec_natDegree
#print axioms OrbitTrace.jordan_linearIndependent
#print axioms OrbitTrace.jordan_span
#print axioms OrbitTrace.jordanElem_delta

end OrbitTrace
