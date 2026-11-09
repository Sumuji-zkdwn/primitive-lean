
/-! Discrete-time eigenfunction pullback through a semiconjugacy. This does not assert a complete spectral representation. -/

namespace LinearInputKoopmanDescent

theorem eigenfunction_pullback {S Q : Type*} (f : S → S) (g : Q → Q)
    (q : S → Q) (h : ∀ s, q (f s) = g (q s))
    (psi : Q → ℝ) (lam : ℝ) (hp : ∀ z, psi (g z) = lam * psi z) (s : S) :
    psi (q (f s)) = lam * psi (q s) := by
  rw [h]
  exact hp (q s)

end LinearInputKoopmanDescent
