/-!
Exact predictive equivalence for the scalar curve-word observation.
The first result is a generic finite-probe criterion for deterministic actions.
-/

namespace LinearInputCurveShadowKernel

open LinearInputOperatorWords (WordEq Respects)

/-- A probe that respects one-step updates makes two readings sufficient for
testing indistinguishability under all finite continuations. -/
theorem two_readings_complete {S O I : Type*} (obs : S → O) (action : I → S → S)
    (probe : I) (closed : Respects (fun s => (obs s, obs (action probe s))) action)
    (s t : S) :
    WordEq obs action s t ↔
      (obs s, obs (action probe s)) = (obs t, obs (action probe t)) := by
  constructor
  · intro h
    exact Prod.ext (h []) (h [probe])
  · intro h
    exact LinearInputOperatorWords.postprocess _ Prod.fst action
      (LinearInputOperatorWords.respects_implies_now_complete _ action closed h)

open LinearInputCurveWordFinite LinearInputCurveWordSampling

abbrev act (a : Bool) (s : State) := step s a
def dir (s : State) : Fin 4 := ⟨s.2.1 % 4, Nat.mod_lt _ (by decide)⟩
def jump (a : Bool) (k : Fin 4) : ℤ :=
  let p := rotate (if a then (3, 3) else (-1, 1)) k
  p.1 + 3 * p.2

private theorem shadow_act (a : Bool) (s : State) :
    shadow (act a s) = shadow s + jump a (dir s) := by
  simp only [act, step, shadow, jump, dir, rotate, Nat.mod_mod]
  ring

private theorem jumpA_injective : ∀ k j : Fin 4, jump true k = jump true j → k = j := by decide

private theorem probe_iff (s t : State) :
    (shadow s, shadow (act true s)) = (shadow t, shadow (act true t)) ↔
      shadow s = shadow t ∧ dir s = dir t := by
  simp only [Prod.mk.injEq, shadow_act]
  constructor
  · rintro ⟨h,e⟩
    rw [h] at e
    exact ⟨h, jumpA_injective _ _ (add_left_cancel e)⟩
  · rintro ⟨h,r⟩
    simp only [h,r,and_self]

private theorem probe_closed : Respects (fun s => (shadow s, shadow (act true s))) act := by
  intro a s t h
  obtain ⟨hz, hd⟩ := (probe_iff s t).mp h
  apply (probe_iff _ _).mpr
  refine ⟨by simp only [shadow_act, hz, hd], ?_⟩
  apply Fin.ext
  change (s.2.1 + _) % 4 = (t.2.1 + _) % 4
  rw [Nat.add_mod s.2.1, Nat.add_mod t.2.1, show s.2.1 % 4 = t.2.1 % 4 from congrArg Fin.val hd]

theorem all_futures_iff_two_readings (s t : State) :
    WordEq shadow act s t ↔
      (shadow s, shadow (act true s)) = (shadow t, shadow (act true t)) :=
  two_readings_complete shadow act true probe_closed s t

theorem all_futures_iff_shadow_heading (s t : State) :
    WordEq shadow act s t ↔ shadow s = shadow t ∧ dir s = dir t :=
  (all_futures_iff_two_readings s t).trans (probe_iff s t)

private theorem clock_invariants (w : List Bool) :
    (state w).2.1 % 2 = w.length % 2 ∧
    ((state w).2.1 : ℤ) % 4 = (shadow (state w) + ↑(w.length % 2)) % 4 := by
  induction w using List.reverseRecOn with
  | nil => decide
  | append_singleton w a ih =>
    have hs : state (w ++ [a]) = step (state w) a := by simp [state]
    simp only [hs, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
    obtain ⟨hp, hc⟩ := ih
    have hlt := Nat.mod_lt (state w).2.1 (by decide : 0 < 4)
    unfold shadow at hc ⊢
    cases a <;> interval_cases k : (state w).2.1 % 4 <;>
      simp [step, rotate, k] <;> omega

/-- The current integer shadow and parity of the number of letters determine the heading. -/
theorem clock_heading (w : List Bool) :
    ((state w).2.1 : ℤ) % 4 = (shadow (state w) + ↑(w.length % 2)) % 4 :=
  (clock_invariants w).2

/-- At a known clock parity on paths starting at the standard initial state,
one scalar is a complete invariant for all common future inputs. -/
theorem same_clock_future_iff (u v : List Bool) (clock : u.length % 2 = v.length % 2) :
    WordEq shadow act (state u) (state v) ↔ shadow (state u) = shadow (state v) := by
  rw [all_futures_iff_shadow_heading]
  refine ⟨And.left, fun hz => ⟨hz, Fin.ext ?_⟩⟩
  have eu := clock_heading u
  have ev := clock_heading v
  rw [clock, hz] at eu
  have eqmod := eu.trans ev.symm
  change (state u).2.1 % 4 = (state v).2.1 % 4
  exact_mod_cast eqmod

/-- Recover an isolated triple from two adjacent samples and clock parity,
even if its preceding word is unknown. -/
theorem two_samples_determine_block (u v : List Bool) (b c : Block)
    (clock : u.length % 2 = v.length % 2)
    (before : shadow (state u) = shadow (state v))
    (after : shadow (advance (state u) b) = shadow (advance (state v) c)) : b = c := by
  have future := (same_clock_future_iff u v clock).mpr before
  have sameEnd : shadow (advance (state u) c) = shadow (advance (state v) c) :=
    future (letters c)
  have traceEq : readings (state u) [b] = readings (state u) [c] := by
    simp only [readings, after.trans sameEnd.symm]
  exact List.cons.inj (readings_injective _ traceEq) |>.1

/-- Without parity, BB and AAA agree now but differ after probing with A. -/
theorem hidden_clock_witness :
    shadow (state [false, false]) = 6 ∧ shadow (state [true, true, true]) = 6 ∧
    shadow (act true (state [false, false])) = -6 ∧
    shadow (act true (state [true, true, true])) = 0 := by decide

end LinearInputCurveShadowKernel
