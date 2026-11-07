/-!
# Descriptive elastica: contextual equality under attachment

States are elastica descriptions (bars).  A context is a finite one-hole
expression built using rewrites and left/right attachment to fixed bars.
The readout is observed only after the context has been applied.

For *total*, deterministic rewriting and attachment:
* contextual equivalence is a congruence for both operations;
* readout, rewrite, and binary attachment descend to its quotient;
* an exact compositional representation cannot merge more states;
* the old operator-word quotient is sufficient for attachment exactly
  when its equivalence is stable under attachment on either side.

The finite Bool x Bool example shows that a correct word-minimal state
is generally NOT closed under attachment.  No geometry, associativity,
smoothness, or physical conservation law is assumed for attachment.
-/

noncomputable section

namespace LinearInputJoinContexts

open LinearInputOperatorWords

/-- One hole, with sequential rewrites or attachment of fixed bars. -/
inductive Context (α ι : Type*) where
  | hole : Context α ι
  | step (i : ι) (c : Context α ι) : Context α ι
  | left (a : α) (c : Context α ι) : Context α ι
  | right (c : Context α ι) (a : α) : Context α ι

/-- Evaluate a context by substituting a bar into its one hole. -/
def plug {α ι : Type*}
    (step : ι → α → α) (join : α → α → α) :
    Context α ι → α → α
  | .hole, x => x
  | .step i c, x => step i (plug step join c x)
  | .left a c, x => join a (plug step join c x)
  | .right c a, x => join (plug step join c x) a

/-- Substitute one one-hole context into another. -/
def compose {α ι : Type*} :
    Context α ι → Context α ι → Context α ι
  | .hole, d => d
  | .step i c, d => .step i (compose c d)
  | .left a c, d => .left a (compose c d)
  | .right c a, d => .right (compose c d) a

theorem plug_compose {α ι : Type*}
    (step : ι → α → α) (join : α → α → α)
    (c d : Context α ι) (x : α) :
    plug step join (compose c d) x =
      plug step join c (plug step join d x) := by
  induction c with
  | hole => rfl
  | step i c ih => simp [compose, plug, ih]
  | left a c ih => simp [compose, plug, ih]
  | right c a ih => simp [compose, plug, ih]

/-- No allowed one-hole context can reveal a readout difference. -/
def ContextEq {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (join : α → α → α)
    (x y : α) : Prop :=
  ∀ c : Context α ι, K (plug step join c x) = K (plug step join c y)

theorem context_refl {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (join : α → α → α)
    (x : α) : ContextEq K step join x x := by
  intro c
  rfl

theorem context_symm {α ω ι : Type*}
    {K : α → ω} {step : ι → α → α} {join : α → α → α}
    {x y : α} (h : ContextEq K step join x y) :
    ContextEq K step join y x := by
  intro c
  exact (h c).symm

theorem context_trans {α ω ι : Type*}
    {K : α → ω} {step : ι → α → α} {join : α → α → α}
    {x y z : α} (hxy : ContextEq K step join x y)
    (hyz : ContextEq K step join y z) :
    ContextEq K step join x z := by
  intro c
  exact (hxy c).trans (hyz c)

/-- Any further context preserves contextual equivalence. -/
theorem context_plug {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (join : α → α → α)
    {x y : α} (h : ContextEq K step join x y)
    (c : Context α ι) :
    ContextEq K step join (plug step join c x) (plug step join c y) := by
  intro d
  have hc := h (compose d c)
  simpa only [plug_compose] using hc

theorem context_now {α ω ι : Type*}
    {K : α → ω} {step : ι → α → α} {join : α → α → α}
    {x y : α} (h : ContextEq K step join x y) : K x = K y := by
  simpa [plug] using h .hole

theorem context_step {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (join : α → α → α)
    {x y : α} (h : ContextEq K step join x y) (i : ι) :
    ContextEq K step join (step i x) (step i y) := by
  simpa [plug] using context_plug K step join h (.step i .hole)

theorem context_left {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (join : α → α → α)
    {x y : α} (h : ContextEq K step join x y) (a : α) :
    ContextEq K step join (join a x) (join a y) := by
  simpa [plug] using context_plug K step join h (.left a .hole)

theorem context_right {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (join : α → α → α)
    {x y : α} (h : ContextEq K step join x y) (a : α) :
    ContextEq K step join (join x a) (join y a) := by
  simpa [plug] using context_plug K step join h (.right .hole a)

/-- Two-sided attachment is a congruence; associativity is not assumed. -/
theorem context_join {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (join : α → α → α)
    {x y z w : α} (hxy : ContextEq K step join x y)
    (hzw : ContextEq K step join z w) :
    ContextEq K step join (join x z) (join y w) := by
  exact context_trans
    (context_right K step join hxy z)
    (context_left K step join hzw y)

/-- Quotient of descriptions by the complete contextual observational kernel. -/
def contextSetoid {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (join : α → α → α) : Setoid α where
  r := ContextEq K step join
  iseqv := ⟨(fun x => context_refl K step join x),
    (fun h => context_symm h),
    (fun hxy hyz => context_trans hxy hyz)⟩

abbrev State {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (join : α → α → α) := Quotient (contextSetoid K step join)

def encode {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (join : α → α → α) (x : α) : State K step join :=
  Quotient.mk (contextSetoid K step join) x

theorem encode_iff {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (join : α → α → α) (x y : α) :
    encode K step join x = encode K step join y ↔ ContextEq K step join x y := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

def readout {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (join : α → α → α) :
    State K step join → ω :=
  Quotient.lift K (by
    intro x y h
    exact context_now h)

def transition {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (join : α → α → α)
    (i : ι) : State K step join → State K step join :=
  Quotient.lift (fun x => encode K step join (step i x)) (by
    intro x y h
    exact Quotient.sound (context_step K step join h i))

/-- Attachment can be done after lossless contextual compression. -/
def attach {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (join : α → α → α) :
    State K step join → State K step join → State K step join :=
  Quotient.lift₂ (fun x y => encode K step join (join x y)) (by
    intro x z y w hxz hyw
    exact Quotient.sound (context_join K step join hxz hyw))

theorem readout_encode {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (join : α → α → α)
    (x : α) :
    readout K step join (encode K step join x) = K x := rfl

theorem transition_encode {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (join : α → α → α)
    (i : ι) (x : α) :
    transition K step join i (encode K step join x) =
      encode K step join (step i x) := rfl

theorem attach_encode {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (join : α → α → α)
    (x y : α) :
    attach K step join (encode K step join x) (encode K step join y) =
      encode K step join (join x y) := rfl

/-- Transport the fixed bars of a context through an exact encoding. -/
def mapContext {α β ι : Type*} (f : α → β) :
    Context α ι → Context β ι
  | .hole => .hole
  | .step i c => .step i (mapContext f c)
  | .left a c => .left (f a) (mapContext f c)
  | .right c a => .right (mapContext f c) (f a)

/-- A homomorphism commutes with every one-hole context evaluation. -/
theorem representation_plug {α β ι : Type*}
    (step : ι → α → α) (join : α → α → α)
    (f : α → β) (update : ι → β → β)
    (combine : β → β → β)
    (hstep : ∀ i x, f (step i x) = update i (f x))
    (hjoin : ∀ x y, f (join x y) = combine (f x) (f y))
    (c : Context α ι) (x : α) :
    f (plug step join c x) =
      plug update combine (mapContext f c) (f x) := by
  induction c with
  | hole => rfl
  | step i c ih =>
      change f (step i (plug step join c x)) =
        update i (plug update combine (mapContext f c) (f x))
      rw [hstep i (plug step join c x), ih]
  | left a c ih =>
      change f (join a (plug step join c x)) =
        combine (f a) (plug update combine (mapContext f c) (f x))
      rw [hjoin a (plug step join c x), ih]
  | right c a ih =>
      change f (join (plug step join c x) a) =
        combine (plug update combine (mapContext f c) (f x)) (f a)
      rw [hjoin (plug step join c x) a, ih]

/-- Any compositional exact representation has at least the distinctions
of the canonical contextual quotient.  No surjectivity is needed. -/
theorem representation_kernel_sub {α β ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (join : α → α → α)
    (f : α → β) (update : ι → β → β) (combine : β → β → β)
    (out : β → ω)
    (hout : ∀ x, out (f x) = K x)
    (hstep : ∀ i x, f (step i x) = update i (f x))
    (hjoin : ∀ x y, f (join x y) = combine (f x) (f y))
    {x y : α} (hxy : f x = f y) :
    ContextEq K step join x y := by
  intro c
  calc
    K (plug step join c x) =
        out (f (plug step join c x)) := (hout _).symm
    _ = out (plug update combine (mapContext f c) (f x)) :=
      congrArg out (representation_plug step join f update combine hstep hjoin c x)
    _ = out (plug update combine (mapContext f c) (f y)) := by rw [hxy]
    _ = out (f (plug step join c y)) :=
      congrArg out (representation_plug step join f update combine hstep hjoin c y).symm
    _ = K (plug step join c y) := hout _

theorem representation_minimal {α β ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (join : α → α → α)
    (f : α → β) (update : ι → β → β) (combine : β → β → β)
    (out : β → ω)
    (hout : ∀ x, out (f x) = K x)
    (hstep : ∀ i x, f (step i x) = update i (f x))
    (hjoin : ∀ x y, f (join x y) = combine (f x) (f y))
    {x y : α} (hxy : f x = f y) :
    encode K step join x = encode K step join y := by
  exact (encode_iff K step join x y).2
    (representation_kernel_sub K step join f update combine out
      hout hstep hjoin hxy)

/-- Every contextual equality also preserves all old rewrite words. -/
theorem context_implies_word {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (join : α → α → α)
    {x y : α} (h : ContextEq K step join x y) :
    WordEq K step x y := by
  have hall : ∀ word : List ι, ∀ a b : α,
      ContextEq K step join a b →
      K (run step word a) = K (run step word b) := by
    intro word
    induction word with
    | nil =>
        intro a b hab
        exact context_now hab
    | cons i rest ih =>
        intro a b hab
        change K (run step rest (step i a)) =
          K (run step rest (step i b))
        exact ih (step i a) (step i b)
          (context_step K step join hab i)
  intro word
  exact hall word x y h

/-- The old word quotient supports a binary attachment precisely when
it is stable under substituting either argument at fixed partner bars. -/
def StableJoin {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (join : α → α → α) : Prop :=
  ∀ x y z, WordEq K step x y →
    WordEq K step (join x z) (join y z) ∧
    WordEq K step (join z x) (join z y)

theorem word_implies_context_of_stable {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (join : α → α → α)
    (hs : StableJoin K step join)
    {x y : α} (h : WordEq K step x y) :
    ContextEq K step join x y := by
  have hall : ∀ c : Context α ι, ∀ a b : α,
      WordEq K step a b →
      WordEq K step (plug step join c a) (plug step join c b) := by
    intro c
    induction c with
    | hole =>
        intro a b hab
        exact hab
    | step i c ih =>
        intro a b hab
        exact word_step (ih a b hab) i
    | left z c ih =>
        intro a b hab
        exact (hs (plug step join c a) (plug step join c b) z (ih a b hab)).2
    | right c z ih =>
        intro a b hab
        exact (hs (plug step join c a) (plug step join c b) z (ih a b hab)).1
  intro c
  exact word_now (hall c x y h)

/-- Criterion: word-based compression is already compositional iff
its observational kernel is stable under left and right attachment. -/
theorem stable_iff_word_context {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (join : α → α → α) :
    StableJoin K step join ↔
      ∀ x y, WordEq K step x y ↔ ContextEq K step join x y := by
  constructor
  · intro hs x y
    exact ⟨word_implies_context_of_stable K step join hs,
      context_implies_word K step join⟩
  · intro hall x y z hxy
    have hc : ContextEq K step join x y := (hall x y).mp hxy
    exact ⟨(hall (join x z) (join y z)).mpr
             (context_right K step join hc z),
           (hall (join z x) (join z y)).mpr
             (context_left K step join hc z)⟩

/-- A binary attachment on the old word quotient, provided its fibers are stable
under replacing either argument. -/
def attachOld {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (join : α → α → α)
    (hs : StableJoin K step join) :
    LinearInputOperatorWords.State K step →
      LinearInputOperatorWords.State K step →
      LinearInputOperatorWords.State K step :=
  Quotient.lift₂
    (fun x y => LinearInputOperatorWords.encode K step (join x y)) (by
      intro x z y w hxz hyw
      have h₁ : WordEq K step (join x z) (join y z) :=
        (hs x y z hxz).1
      have h₂ : WordEq K step (join y z) (join y w) :=
        (hs z w y hyw).2
      exact Quotient.sound (word_trans h₁ h₂))

theorem attachOld_encode {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (join : α → α → α)
    (hs : StableJoin K step join) (x y : α) :
    attachOld K step join hs
      (LinearInputOperatorWords.encode K step x)
      (LinearInputOperatorWords.encode K step y) =
        LinearInputOperatorWords.encode K step (join x y) := rfl

/-- Exact descent theorem: the old predictive quotient admits the original
binary attachment iff its observational equivalence is a join congruence. -/
theorem stable_iff_old_attach_exists {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (join : α → α → α) :
    StableJoin K step join ↔
      ∃ A : LinearInputOperatorWords.State K step →
          LinearInputOperatorWords.State K step →
          LinearInputOperatorWords.State K step,
        ∀ x y : α,
          A (LinearInputOperatorWords.encode K step x)
            (LinearInputOperatorWords.encode K step y) =
              LinearInputOperatorWords.encode K step (join x y) := by
  constructor
  · intro hs
    exact ⟨attachOld K step join hs, attachOld_encode K step join hs⟩
  · rintro ⟨A, hA⟩ x y z hxy
    have hclass : LinearInputOperatorWords.encode K step x =
        LinearInputOperatorWords.encode K step y :=
      (LinearInputOperatorWords.encode_eq_iff K step x y).2 hxy
    constructor
    · apply (LinearInputOperatorWords.encode_eq_iff K step
        (join x z) (join y z)).1
      calc
        LinearInputOperatorWords.encode K step (join x z) =
          A (LinearInputOperatorWords.encode K step x)
            (LinearInputOperatorWords.encode K step z) := (hA x z).symm
        _ = A (LinearInputOperatorWords.encode K step y)
            (LinearInputOperatorWords.encode K step z) :=
              congrArg (fun q => A q (LinearInputOperatorWords.encode K step z)) hclass
        _ = LinearInputOperatorWords.encode K step (join y z) := hA y z
    · apply (LinearInputOperatorWords.encode_eq_iff K step
        (join z x) (join z y)).1
      calc
        LinearInputOperatorWords.encode K step (join z x) =
          A (LinearInputOperatorWords.encode K step z)
            (LinearInputOperatorWords.encode K step x) := (hA z x).symm
        _ = A (LinearInputOperatorWords.encode K step z)
            (LinearInputOperatorWords.encode K step y) :=
              congrArg (A (LinearInputOperatorWords.encode K step z)) hclass
        _ = LinearInputOperatorWords.encode K step (join z y) := hA z y

/-- Four concrete bars.  The second bit is invisible until an attachment
with a partner whose first bit is true flips the first-bit readout. -/
def exK (x : Bool × Bool) : Bool := x.1

def exStep : Unit → Bool × Bool → Bool × Bool := fun _ x => x

def exJoin (x y : Bool × Bool) : Bool × Bool :=
  (if x.2 && y.1 then !x.1 else x.1, x.2)

def exA : Bool × Bool := (false, false)
def exB : Bool × Bool := (false, true)
def exZ : Bool × Bool := (true, false)

theorem ex_run (word : List Unit) (x : Bool × Bool) :
    run exStep word x = x := by
  induction word with
  | nil => rfl
  | cons i rest ih =>
      change run exStep rest x = x
      exact ih

theorem ex_word_equal : WordEq exK exStep exA exB := by
  intro word
  rw [ex_run, ex_run]
  decide

/-- Mere rewrite-word equivalence fails under joining with exZ. -/
theorem ex_context_separates :
    ¬ ContextEq exK exStep exJoin exA exB := by
  intro h
  have hne :
      exK (plug exStep exJoin (.right .hole exZ) exA) ≠
        exK (plug exStep exJoin (.right .hole exZ) exB) := by decide
  exact hne (h (.right .hole exZ))

theorem ex_join_not_stable : ¬ StableJoin exK exStep exJoin := by
  intro hs
  exact ex_context_separates
    (word_implies_context_of_stable exK exStep exJoin hs ex_word_equal)

end LinearInputJoinContexts
