/-!
# Exact observations of compatible inverse towers

The limit below is a set of compatible coordinate sequences. A family of
updates commuting with the bonding maps acts on that set; each projection
is then an exact bridge to an existing deterministic observation system.
The multiple-action version connects to the existing operator-word API.

A finite Boolean-prefix tower supplies explicit compatible states,
noninjective projections and a nontrivial compatible flip action.
No topology, metric, measure, Laakso space or geometric limit is constructed.
In particular, compatibility of an actual proposed dynamics must be proved
separately; the tower does not force that compatibility.
-/

noncomputable section

namespace LinearInputInverseTowerObservation

universe u v w

variable (X : ℕ → Type u) (p : (n : ℕ) → X (n + 1) → X n)

/-- Compatible sequences, without an assumed topology or distance. -/
def Limit := {x : (n : ℕ) → X n // ∀ n, p n (x (n + 1)) = x n}

def project (n : ℕ) (x : Limit X p) : X n := x.val n

theorem project_compatible (n : ℕ) (x : Limit X p) :
    p n (project X p (n + 1) x) = project X p n x := x.property n

section SingleUpdate

variable (U : (n : ℕ) → X n → X n)
variable (hU : ∀ n z, p n (U (n + 1) z) = U n (p n z))

/-- A compatible family acts coordinatewise on compatible sequences. -/
def update (x : Limit X p) : Limit X p :=
  ⟨fun n => U n (x.val n), fun n => by
    calc
      p n (U (n + 1) (x.val (n + 1))) = U n (p n (x.val (n + 1))) := hU n _
      _ = U n (x.val n) := congrArg (U n) (x.property n)⟩

/-- Every projection is an exact semiconjugacy. -/
theorem project_update (n : ℕ) (x : Limit X p) :
    project X p n (update X p U hU x) = U n (project X p n x) := rfl

/-- The existing representation theorem supplies all finite times. -/
theorem project_iterate (n t : ℕ) (x : Limit X p) :
    project X p n ((update X p U hU)^[t] x) =
      (U n)^[t] (project X p n x) :=
  LinearInputFutureObservation.representation_iterate
    (update X p U hU) (U n) (project X p n) (project_update X p U hU n) t x

/-- Existing predictive-kernel minimality applies at every level. -/
theorem same_projection_same_future (n : ℕ) {ω : Type v} (K : X n → ω)
    {x y : Limit X p} (hxy : project X p n x = project X p n y) :
    LinearInputFutureObservation.FutureEq
      (fun z => K (project X p n z)) (update X p U hU) x y :=
  LinearInputFutureObservation.predictive_kernel_sub
    (fun z => K (project X p n z)) (update X p U hU)
    (project X p n) (U n) K (fun _ => rfl)
    (project_update X p U hU n) hxy

theorem projected_future_iff (n : ℕ) {ω : Type v} (K : X n → ω)
    (x y : Limit X p) :
    LinearInputFutureObservation.FutureEq
      (fun z => K (project X p n z)) (update X p U hU) x y ↔
    LinearInputFutureObservation.FutureEq K (U n)
      (project X p n x) (project X p n y) := by
  constructor
  · intro h t
    have ht := h t
    change K (project X p n ((update X p U hU)^[t] x)) =
      K (project X p n ((update X p U hU)^[t] y)) at ht
    simpa only [project_iterate] using ht
  · intro h t
    change K (project X p n ((update X p U hU)^[t] x)) =
      K (project X p n ((update X p U hU)^[t] y))
    simpa only [project_iterate] using h t

end SingleUpdate

/-- The complete family of coordinates separates compatible sequences. -/
theorem all_projections_separate (x y : Limit X p) :
    (∀ n, project X p n x = project X p n y) ↔ x = y := by
  constructor
  · intro h
    apply Subtype.ext
    funext n
    exact h n
  · intro h
    subst y
    intro n
    rfl

section MultipleActions

variable {ι : Type w} (step : ι → (n : ℕ) → X n → X n)
variable (hstep : ∀ i n z, p n (step i (n + 1) z) = step i n (p n z))

/-- Lift each compatible action to the set-level limit. -/
def action (i : ι) : Limit X p → Limit X p :=
  update X p (step i) (hstep i)

/-- Every projection is an exact bridge for the whole action alphabet. -/
theorem project_exactBridge (n : ℕ) {ω : Type v} (K : X n → ω) :
    LinearInputCrossSystemObservation.ExactBridge
      (fun z => K (project X p n z)) K
      (action X p step hstep) (fun i => step i n) (project X p n) :=
  ⟨fun _ => rfl, fun _ _ => rfl⟩

/-- Projecting commutes with every finite action word. -/
theorem project_run (n : ℕ) (word : List ι) (x : Limit X p) :
    project X p n (LinearInputOperatorWords.run (action X p step hstep) word x) =
      LinearInputOperatorWords.run (fun i => step i n) word (project X p n x) :=
  LinearInputCrossSystemObservation.bridge_run
    (project X p n) (fun z => z) (action X p step hstep)
    (fun i => step i n) (project X p n)
    (project_exactBridge X p step hstep n (fun z => z)) word x

/-- The lifted and level systems have exactly matching projected word kernels. -/
theorem projected_wordEq_iff (n : ℕ) {ω : Type v} (K : X n → ω)
    (x y : Limit X p) :
    LinearInputOperatorWords.WordEq (fun z => K (project X p n z))
      (action X p step hstep) x y ↔
    LinearInputOperatorWords.WordEq K (fun i => step i n)
      (project X p n x) (project X p n y) :=
  ⟨LinearInputCrossSystemObservation.bridge_preserves_wordEq
      _ _ _ _ _ (project_exactBridge X p step hstep n K),
    LinearInputCrossSystemObservation.bridge_reflects_wordEq
      _ _ _ _ _ (project_exactBridge X p step hstep n K)⟩

end MultipleActions

section BooleanPrefixes

/-- The nth level contains exactly the first n Boolean coordinates. -/
def BitLevel (n : ℕ) := Fin n → Bool

def dropLast (n : ℕ) (x : BitLevel (n + 1)) : BitLevel n :=
  fun i => x i.castSucc

/-- Any infinite bit stream gives an explicit compatible sequence. -/
def bitLimit (s : ℕ → Bool) : Limit BitLevel dropLast :=
  ⟨fun _ i => s i.val, fun _ => rfl⟩

/-- False leaves each bit fixed; true complements every bit. -/
def bitStep (flip : Bool) (n : ℕ) (x : BitLevel n) : BitLevel n :=
  fun i => if flip then !(x i) else x i

theorem bitStep_compatible (flip : Bool) (n : ℕ) (x : BitLevel (n + 1)) :
    dropLast n (bitStep flip (n + 1) x) = bitStep flip n (dropLast n x) := rfl

/-- The explicit two-action family satisfies the exact-bridge contract. -/
theorem bit_project_exactBridge (n : ℕ) :
    LinearInputCrossSystemObservation.ExactBridge
      (project BitLevel dropLast n) (fun x => x)
      (action BitLevel dropLast bitStep bitStep_compatible)
      (fun flip => bitStep flip n) (project BitLevel dropLast n) :=
  project_exactBridge BitLevel dropLast bitStep bitStep_compatible n (fun x => x)

theorem bit_action_false (x : Limit BitLevel dropLast) :
    action BitLevel dropLast bitStep bitStep_compatible false x = x := by
  apply Subtype.ext
  funext n i
  rfl

theorem bit_action_true_changes_zero :
    action BitLevel dropLast bitStep bitStep_compatible true (bitLimit (fun _ => false)) ≠
      bitLimit (fun _ => false) := by
  intro h
  have hb := congrArg (fun x => project BitLevel dropLast 1 x 0) h
  exact Bool.noConfusion hb

/-- Every finite projection loses a bit, despite being an exact action bridge. -/
theorem bit_project_not_injective (n : ℕ) :
    ¬ Function.Injective (project BitLevel dropLast n) := by
  intro hinj
  have hp : project BitLevel dropLast n (bitLimit (fun _ => false)) =
      project BitLevel dropLast n (bitLimit (fun k => decide (k = n))) := by
    funext i
    have hi : i.val ≠ n := Nat.ne_of_lt i.isLt
    simp only [project, bitLimit, hi, decide_false]
  have heq := hinj hp
  have hb := congrArg (fun x => project BitLevel dropLast (n + 1) x (Fin.last n)) heq
  have hfalse : false = true := by simpa only [project, bitLimit, Fin.val_last, decide_true] using hb
  exact Bool.noConfusion hfalse

end BooleanPrefixes

end LinearInputInverseTowerObservation
