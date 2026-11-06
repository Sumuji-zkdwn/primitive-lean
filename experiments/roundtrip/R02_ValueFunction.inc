/-!
# Round trip 2: interpolation line → lower envelope → concave value function

Input: round 1 says each state contributes an affine function `u ↦ A z - u X z`.
Translation (convex analysis): the minimum value over states is the lower envelope
of affine lines, hence concave, and `-X(z_u)` is a supergradient at `u`.
Back-translation: the baseline `minimizer_monotone` (for `S = ℝ`, `X = id`) becomes the
case of monotone supergradients for an arbitrary state space and observable `X`.
Additional hypothesis: minimizers are assumed to exist; nothing here proves existence.
-/

noncomputable section
namespace RoundTrip02
open LinearInputObservation

/-- `z` is a global minimizer of the observation at input `u`. -/
def IsMinimizer {S : Type*} (A X : S → ℝ) (u : ℝ) (z : S) : Prop :=
  ∀ w, energy A X u z ≤ energy A X u w

/-- Supergradient inequality for the minimum value. Only `zv` needs to minimize. -/
theorem supergradient {S : Type*} (A X : S → ℝ) {v : ℝ} {zv : S}
    (hv : IsMinimizer A X v zv) (u : ℝ) (zu : S) :
    energy A X v zv ≤ energy A X u zu - (v - u) * X zu := by
  have h := hv zu
  unfold energy at *
  linarith

/-- Monotone supergradients, for an arbitrary state space and observable. -/
theorem observable_monotone {S : Type*} (A X : S → ℝ) {u v : ℝ} {zu zv : S}
    (hu : IsMinimizer A X u zu) (hv : IsMinimizer A X v zv) :
    0 ≤ (v - u) * (X zv - X zu) := by
  have h1 := supergradient A X hv u zu
  have h2 := supergradient A X hu v zv
  nlinarith

/-- Back-translation: the baseline theorem is recovered as the instance `S = ℝ`, `X = id`. -/
theorem minimizer_monotone_from_envelope (V : ℝ → ℝ) (u v xu xv : ℝ) (huv : u < v)
    (hu : ∀ x, V xu - u * xu ≤ V x - u * x)
    (hv : ∀ x, V xv - v * xv ≤ V x - v * x) :
    xu ≤ xv := by
  have h := observable_monotone V id (u := u) (v := v) (zu := xu) (zv := xv)
    (fun w => by simpa [energy] using hu w) (fun w => by simpa [energy] using hv w)
  simp only [id] at h
  have hpos : 0 < v - u := sub_pos.mpr huv
  by_contra hn
  have hneg : xv - xu < 0 := by linarith [lt_of_not_ge hn]
  nlinarith

/-- Concavity of the minimum value along a segment of inputs. The bound holds for
every state `zw`, in particular for a minimizer at the intermediate input; no
minimality at `t * u + (1 - t) * v` is needed. -/
theorem value_concave {S : Type*} (A X : S → ℝ) {u v t : ℝ} {zu zv : S}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hu : IsMinimizer A X u zu) (hv : IsMinimizer A X v zv) (zw : S) :
    t * energy A X u zu + (1 - t) * energy A X v zv ≤
      energy A X (t * u + (1 - t) * v) zw := by
  have h1 := hu zw
  have h2 := hv zw
  have h1' := mul_le_mul_of_nonneg_left h1 ht0
  have h2' := mul_le_mul_of_nonneg_left h2 (sub_nonneg.mpr ht1)
  unfold energy at *
  nlinarith

end RoundTrip02
