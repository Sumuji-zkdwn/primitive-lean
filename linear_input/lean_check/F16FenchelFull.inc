/-!
Full 16-dimensional Legendre-Fenchel dual of the actual signed F16 pencil.

The finite Fenchel domain is the range of the normal operator A* A,
equivalently the orthogonal complement of ker A. The supremum is attained
at every normal-equation solution, and is independent of that choice.

No generalized-inverse routine, extra axiom, or unsupported physical
interpretation is assumed. The input A_t is the original exact F16 matrix.
-/

noncomputable section
open Real Set

namespace LinearInputF16FenchelFull

open LinearInputF16Determinant LinearInputF16CompleteRank

abbrev State := EuclideanSpace ℝ (Fin 16)

/-- The actual signed left pencil L_(e3 + t e10) on 16 real coordinates. -/
def action (t : ℝ) : State →ₗ[ℝ] State :=
  (realPencilAll t).toEuclideanLin

/-- Normal operator, with respect to the standard Euclidean inner product. -/
def normal (t : ℝ) : State →ₗ[ℝ] State :=
  (action t).adjoint ∘ₗ action t

def potential (t : ℝ) (z : State) : ℝ :=
  ⟪action t z, action t z⟫_ℝ / 2

def score (t : ℝ) (p z : State) : ℝ :=
  ⟪p, z⟫_ℝ - potential t z

/-- The exact normal equation, expressed with the real Euclidean adjoint. -/
theorem inner_normal (t : ℝ) (z w : State) :
    ⟪normal t z, w⟫_ℝ = ⟪action t z, action t w⟫_ℝ := by
  change ⟪(action t).adjoint ((action t) z), w⟫_ℝ =
    ⟪(action t) z, (action t) w⟫_ℝ
  exact (action t).adjoint_inner_left w ((action t) z)

/-- Exact completion of the square in all sixteen coordinates. -/
theorem score_square_identity (t : ℝ) (z w : State) :
    score t (normal t z) w =
      potential t z -
        ⟪action t (w - z), action t (w - z)⟫_ℝ / 2 := by
  have hd : action t (w - z) = action t w - action t z := by simp
  rw [hd, real_inner_sub_sub_self]
  simp only [score, potential, inner_normal]
  rw [real_inner_comm (action t z) (action t w)]
  ring

theorem score_upper (t : ℝ) (z w : State) :
    score t (normal t z) w ≤ potential t z := by
  rw [score_square_identity]
  have hn : 0 ≤ ⟪action t (w - z), action t (w - z)⟫_ℝ :=
    real_inner_self_nonneg
  linarith

theorem score_attained (t : ℝ) (z : State) :
    score t (normal t z) z = potential t z := by
  rw [score_square_identity]
  simp

/-- The supremum is attained and equals the potential at any normal solution. -/
theorem conjugate_eq_of_normal (t : ℝ) (z : State) :
    sSup (Set.range (score t (normal t z))) = potential t z := by
  apply IsGreatest.csSup_eq
  constructor
  · exact ⟨z, score_attained t z⟩
  · rintro a ⟨w, rfl⟩
    exact score_upper t z w

/-- The correct space of finite dual parameters, without a pseudoinverse. -/
theorem normal_range_eq_orthogonal_kernel (t : ℝ) :
    (normal t).range = (action t).kerᗮ := by
  change ((action t).adjoint ∘ₗ action t).range = (action t).kerᗮ
  calc
    _ = (action t).adjoint.range := (action t).range_adjoint_comp_self
    _ = _ := (action t).orthogonal_ker.symm

/-- Along a null direction the quadratic term is exactly zero. -/
theorem score_kernel_ray (t : ℝ) (p w : State)
    (hw : w ∈ (action t).ker) (r : ℝ) :
    score t p (r • w) = r * ⟪p, w⟫_ℝ := by
  have hzero : action t w = 0 := LinearMap.mem_ker.mp hw
  simp [score, potential, hzero, real_inner_smul_right]

/-- A sharp necessary and sufficient condition for the full 16D dual score
to be bounded above. Unlike the selected 2D section, this detects the
t=-1 degeneracy as well. -/
theorem score_bddAbove_iff (t : ℝ) (p : State) :
    BddAbove (Set.range (score t p)) ↔ p ∈ (normal t).range := by
  constructor
  · intro hb
    by_contra hn
    have hnot : p ∉ (action t).kerᗮ := by
      rw [← normal_range_eq_orthogonal_kernel t]
      exact hn
    have hwitness : ∃ w : State, w ∈ (action t).ker ∧ ⟪p, w⟫_ℝ ≠ 0 := by
      by_contra h
      apply hnot
      apply (Submodule.mem_orthogonal' ((action t).ker) p).mpr
      intro w hw
      by_contra hpair
      exact h ⟨w, hw, hpair⟩
    obtain ⟨w, hw, hpw⟩ := hwitness
    obtain ⟨B, hB⟩ := hb
    let r : ℝ := (B + 1) / ⟪p, w⟫_ℝ
    have hs : score t p (r • w) = B + 1 := by
      rw [score_kernel_ray t p w hw r]
      dsimp [r]
      field_simp [hpw]
    have hu : score t p (r • w) ≤ B :=
      hB (Set.mem_range.mpr ⟨r • w, rfl⟩)
    linarith
  · intro h
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp h
    refine ⟨potential t z, ?_⟩
    rintro a ⟨w, rfl⟩
    rw [← hz]
    exact score_upper t z w

/-- An exact 16D Fenchel value theorem whenever the dual is finite. -/
theorem conjugate_of_bddAbove (t : ℝ) (p : State)
    (hp : BddAbove (Set.range (score t p))) :
    ∃ z : State, normal t z = p ∧
      sSup (Set.range (score t p)) = potential t z := by
  obtain ⟨z, hz⟩ := LinearMap.mem_range.mp ((score_bddAbove_iff t p).mp hp)
  refine ⟨z, hz, ?_⟩
  rw [← hz]
  exact conjugate_eq_of_normal t z

/-- Although normal solutions can be non-unique at singular t, the
dual value is invariant under the choice of a solution. -/
theorem potential_eq_of_same_normal (t : ℝ) (z w : State)
    (h : normal t z = normal t w) :
    potential t z = potential t w := by
  calc
    potential t z = sSup (Set.range (score t (normal t z))) :=
      (conjugate_eq_of_normal t z).symm
    _ = sSup (Set.range (score t (normal t w))) := by rw [h]
    _ = potential t w := conjugate_eq_of_normal t w

/-- The original full F16 matrix loses exactly four ranks at either singular parameter. -/
theorem left_pencil_rank (t : ℝ) :
    (realPencilAll t).rank =
      if t = 1 ∨ t = -1 then 12 else 16 :=
  rank_classification t

end LinearInputF16FenchelFull
