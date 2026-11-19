/-!
Two observations of a cross-hatched board recover its dimensions.
Coordinates below are doubled Cartesian coordinates. A rectangle of diagonal
side lengths `a,b` with lower-left bounding-box corner `(x,y)` has vertices
`(x,y+b), (x+a,y+b+a), (x+b,y), (x+a+b,y+a)`. Thus its bounding box has
side `a+b`, and all four vertices lie on the cross-hatched vertex lattice
(both coordinates of the same parity) precisely when `x ≡ y+b (mod 2)`.
For fixed positive side lengths the bounding-box corner determines the rectangle.
-/

namespace LinearInputCrosshatchedRecovery

def latticePoint (m n x y : ℕ) : Prop := x ≤ 2*m ∧ y ≤ 2*n ∧ x%2 = y%2

/-- Test all four vertices in the actual board in doubled Cartesian coordinates. -/
theorem corners_mem_iff (m n a b x y : ℕ) :
    (latticePoint m n x (y+b) ∧ latticePoint m n (x+a) (y+b+a) ∧
     latticePoint m n (x+b) y ∧ latticePoint m n (x+a+b) (y+a)) ↔
      x+a+b ≤ 2*m ∧ y+a+b ≤ 2*n ∧ x%2 = (y+b)%2 := by
  unfold latticePoint
  omega

@[ext] structure Placement (m n a b : ℕ) where
  x : ℕ
  y : ℕ
  x_bound : x + a + b ≤ 2 * m
  y_bound : y + a + b ≤ 2 * n
  vertex : x % 2 = (y + b) % 2

/-- Number of admissible coordinates of parity `r` along one side. -/
private def span (d l r : ℕ) := (2 * d + 2 - (l + r)) / 2

private theorem half_lt_span {x d a b r : ℕ}
    (h : x + a + b ≤ 2 * d) (hr : x % 2 = r) :
    x / 2 < span d (a + b) r := by
  unfold span
  omega

private theorem expand_bound {i d a b r : ℕ}
    (hi : i < span d (a + b) r) : 2 * i + r + a + b ≤ 2 * d := by
  unfold span at hi
  omega

private def PhaseBox (m n a b r : ℕ) :=
  Fin (span m (a + b) r) × Fin (span n (a + b) ((r + b) % 2))

private def pack {m n a b : ℕ} (p : Placement m n a b) (r : ℕ)
    (h : p.x % 2 = r) : PhaseBox m n a b r :=
  (⟨p.x / 2, half_lt_span p.x_bound h⟩,
   ⟨p.y / 2, half_lt_span p.y_bound (by have := p.vertex; omega)⟩)

private def unpack {m n a b r : ℕ} (z : PhaseBox m n a b r) :
    Placement m n a b where
  x := 2 * z.1.val + r
  y := 2 * z.2.val + (r + b) % 2
  x_bound := expand_bound z.1.isLt
  y_bound := expand_bound z.2.isLt
  vertex := by omega

private def parityEquiv (m n a b : ℕ) :
    Placement m n a b ≃ PhaseBox m n a b 0 ⊕ PhaseBox m n a b 1 where
  toFun p := if h : p.x % 2 = 0 then .inl (pack p 0 h)
             else .inr (pack p 1 (by omega))
  invFun := Sum.elim (unpack (r := 0)) (unpack (r := 1))
  left_inv p := by
    have hp := p.vertex
    dsimp only
    split <;> apply Placement.ext <;> dsimp [unpack, pack] <;> omega
  right_inv z := by
    rcases z with z | z
    · have hx : (unpack (r := 0) z).x % 2 = 0 := by dsimp [unpack]; omega
      dsimp only [Sum.elim_inl]
      rw [dite_eq_left hx, Sum.inl.injEq]
      apply Prod.ext <;> apply Fin.ext <;> dsimp [pack, unpack] <;> omega
    · have hx : (unpack (r := 1) z).x % 2 ≠ 0 := by dsimp [unpack]; omega
      dsimp only [Sum.elim_inr]
      rw [dite_eq_right hx, Sum.inr.injEq]
      apply Prod.ext <;> apply Fin.ext <;> dsimp [pack, unpack] <;> omega

/-- The first size class consists of the diagonal unit squares. -/
noncomputable def c₂ (m n : ℕ) := Nat.card (Placement m n 1 1)

/-- The next class admits the two diagonal orientations of a 1-by-2 rectangle. -/
noncomputable def c₃ (m n : ℕ) := Nat.card (Placement m n 1 2) + Nat.card (Placement m n 2 1)

private theorem placement_card (m n a b : ℕ) :
    Nat.card (Placement m n a b) =
      span m (a+b) 0 * span n (a+b) ((0+b)%2) +
      span m (a+b) 1 * span n (a+b) ((1+b)%2) := by
  rw [Nat.card_congr (parityEquiv m n a b)]
  simp [PhaseBox, Nat.card_eq_fintype_card]

theorem c₂_succ (m n : ℕ) : c₂ (m+1) (n+1) = (m+1)*n + m*(n+1) := by
  rw [c₂, placement_card]
  have h0 (i : ℕ) : span (i+1) 2 0 = i+1 := by unfold span; omega
  have h1 (i : ℕ) : span (i+1) 2 1 = i := by unfold span; omega
  change span (m+1) 2 0 * span (n+1) 2 1 + span (m+1) 2 1 * span (n+1) 2 0 = _
  rw [h0, h0, h1, h1]

theorem c₃_succ (m n : ℕ) : c₃ (m+1) (n+1) = 4*m*n := by
  rw [c₃, placement_card, placement_card]
  have h0 (i : ℕ) : span (i+1) 3 0 = i := by unfold span; omega
  have h1 (i : ℕ) : span (i+1) 3 1 = i := by unfold span; omega
  change (span (m+1) 3 0 * span (n+1) 3 0 + span (m+1) 3 1 * span (n+1) 3 1) +
    (span (m+1) 3 0 * span (n+1) 3 1 + span (m+1) 3 1 * span (n+1) 3 0) = _
  simp only [h0, h1]
  ring

/-- Integer identities for recovering first the sum and then the product of the side lengths. -/
theorem recover_sum_product (m n : ℕ) :
    2*((m+1)+(n+1)) + c₃ (m+1) (n+1) = 2*c₂ (m+1) (n+1) + 4 ∧
    2*((m+1)*(n+1)) = c₂ (m+1) (n+1) + ((m+1)+(n+1)) := by
  rw [c₂_succ, c₃_succ]
  constructor <;> ring

/-- Use ordered dimensions to express recovery up to exchanging the board axes. -/
abbrev Board := {d : ℕ × ℕ // 0 < d.1 ∧ d.1 ≤ d.2}

noncomputable def firstCount (d : Board) : ℕ := c₂ d.1.1 d.1.2
noncomputable def secondCount (d : Board) : ℕ := c₃ d.1.1 d.1.2

private theorem sides_eq {m n u v : ℕ} (hmn : m ≤ n) (huv : u ≤ v)
    (hs : m+n = u+v) (hp : m*n = u*v) : m = u ∧ n = v := by
  have hs' : (m : ℤ) + n = u + v := by exact_mod_cast hs
  have hp' : (m : ℤ) * n = u * v := by exact_mod_cast hp
  have hz : ((m : ℤ) - u) * (m - v) = 0 := by
    calc
      _ = (m : ℤ)^2 - m*(u+v) + u*v := by ring
      _ = 0 := by rw [← hs', ← hp']; ring
  rcases mul_eq_zero.mp hz with h | h <;> omega

theorem counts_recover : Function.Injective
    (LinearInputFiniteObservation.joint firstCount secondCount) := by
  apply (LinearInputFiniteObservation.joint_injective_iff _ _).2
  rintro ⟨⟨m,n⟩, hm, hmn⟩ ⟨⟨u,v⟩, hu, huv⟩ h₂ h₃
  change 0 < m at hm
  change m ≤ n at hmn
  change 0 < u at hu
  change u ≤ v at huv
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : u ≠ 0)
  obtain ⟨v, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : v ≠ 0)
  change c₂ (m+1) (n+1) = c₂ (u+1) (v+1) at h₂
  change c₃ (m+1) (n+1) = c₃ (u+1) (v+1) at h₃
  simp only [c₂_succ, c₃_succ, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one,
    Nat.mul_assoc] at h₂ h₃
  have hp : m*n = u*v := by omega
  obtain ⟨rfl, rfl⟩ := sides_eq (m := m) (n := n) (u := u) (v := v)
    (by omega) (by omega) (by omega) hp
  rfl

theorem first_count_collision :
    c₂ 1 8 = c₂ 2 3 ∧ c₃ 1 8 = 0 ∧ c₃ 2 3 = 8 := by
  change c₂ (0+1) (7+1) = c₂ (1+1) (2+1) ∧
    c₃ (0+1) (7+1) = 0 ∧ c₃ (1+1) (2+1) = 8
  rw [c₂_succ, c₂_succ, c₃_succ, c₃_succ]
  decide

theorem second_count_collision :
    c₃ 2 5 = c₃ 3 3 ∧ c₂ 2 5 = 13 ∧ c₂ 3 3 = 12 := by
  change c₃ (1+1) (4+1) = c₃ (2+1) (2+1) ∧
    c₂ (1+1) (4+1) = 13 ∧ c₂ (2+1) (2+1) = 12
  rw [c₃_succ, c₃_succ, c₂_succ, c₂_succ]
  decide

end LinearInputCrosshatchedRecovery
