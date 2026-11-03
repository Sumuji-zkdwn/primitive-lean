/-!
# Arbitrary sensor families and the observation-kernel intersection

An indexed family of observation channels is represented by the
function-valued readout `fun x i => sensor i x`. Its complete word
kernel is exactly the intersection of all constituent word kernels.

This holds for arbitrary (including infinite) families of sensors and
arbitrary (including infinite) alphabets of deterministic operators.
Joint injectivity gives full state identification; independent sensors
may jointly identify states that neither channel can distinguish.
-/

noncomputable section

namespace LinearInputOperatorSensors

open LinearInputOperatorWords

/-- Evaluate every observation channel on the same state. -/
def bundle {α ω δ : Type*} (sensor : δ → α → ω)
    (x : α) : δ → ω := fun i => sensor i x

/-- Projections of a bundled output recover the original channel values. -/
theorem bundle_apply {α ω δ : Type*}
    (sensor : δ → α → ω) (i : δ) (x : α) :
    bundle sensor x i = sensor i x := rfl

/-- Bundled word equivalence is the intersection over every sensor. -/
theorem bundle_wordEq_iff {α ω ι δ : Type*}
    (sensor : δ → α → ω) (step : ι → α → α)
    (x y : α) :
    WordEq (bundle sensor) step x y ↔
      ∀ i : δ, WordEq (sensor i) step x y := by
  constructor
  · intro h i word
    exact congrFun (h word) i
  · intro h word
    funext i
    exact h i word

/-- Each original sensor is no more discriminating than its bundle. -/
theorem bundle_implies_sensor {α ω ι δ : Type*}
    (sensor : δ → α → ω) (step : ι → α → α)
    {x y : α} (h : WordEq (bundle sensor) step x y)
    (i : δ) : WordEq (sensor i) step x y :=
  (bundle_wordEq_iff sensor step x y).1 h i

/-- A subfamily obtained by relabelling cannot reveal extra distinctions. -/
theorem bundle_reindex {α ω ι δ ε : Type*}
    (sensor : δ → α → ω) (index : ε → δ)
    (step : ι → α → α) {x y : α}
    (h : WordEq (bundle sensor) step x y) :
    WordEq (bundle (fun j => sensor (index j))) step x y := by
  apply (bundle_wordEq_iff _ step x y).2
  intro j
  exact bundle_implies_sensor sensor step h (index j)

/-- A surjective channel reindexing preserves the full observation kernel. -/
theorem bundle_reindex_surjective {α ω ι δ ε : Type*}
    (sensor : δ → α → ω) (index : ε → δ)
    (hi : Function.Surjective index)
    (step : ι → α → α) (x y : α) :
    WordEq (bundle (fun j => sensor (index j))) step x y ↔
      WordEq (bundle sensor) step x y := by
  constructor
  · intro h
    apply (bundle_wordEq_iff sensor step x y).2
    intro i
    obtain ⟨j,hj⟩ := hi i
    have hJ := (bundle_wordEq_iff _ step x y).1 h j
    simpa [hj] using hJ
  · exact bundle_reindex sensor index step

/-- Concatenating two sensor libraries intersects their kernels. -/
theorem bundle_sum_iff {α ω ι δ ε : Type*}
    (A : δ → α → ω) (B : ε → α → ω)
    (step : ι → α → α) (x y : α) :
    WordEq (bundle (fun s : Sum δ ε =>
      match s with
      | Sum.inl i => A i
      | Sum.inr j => B j)) step x y ↔
      WordEq (bundle A) step x y ∧
        WordEq (bundle B) step x y := by
  constructor
  · intro h
    have hh := (bundle_wordEq_iff _ step x y).1 h
    constructor
    · apply (bundle_wordEq_iff A step x y).2
      intro i
      exact hh (Sum.inl i)
    · apply (bundle_wordEq_iff B step x y).2
      intro j
      exact hh (Sum.inr j)
  · rintro ⟨hA,hB⟩
    apply (bundle_wordEq_iff _ step x y).2
    intro s
    cases s with
    | inl i => exact (bundle_wordEq_iff A step x y).1 hA i
    | inr j => exact (bundle_wordEq_iff B step x y).1 hB j

/-- A single sensor has precisely its own observational kernel. -/
theorem bundle_unit_iff {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (x y : α) :
    WordEq (bundle (fun _ : Unit => K)) step x y ↔
      WordEq K step x y := by
  constructor
  · intro h
    exact bundle_implies_sensor _ step h ()
  · intro h
    apply (bundle_wordEq_iff _ step x y).2
    intro i
    cases i
    exact h

/-- If the current sensor bundle is injective, all words are unnecessary
for state identification. -/
theorem bundle_wordEq_implies_eq {α ω ι δ : Type*}
    (sensor : δ → α → ω) (step : ι → α → α)
    (h : Function.Injective (bundle sensor))
    {x y : α}
    (hxy : WordEq (bundle sensor) step x y) : x = y :=
  h (word_now hxy)

/-- A single injective sensor fully distinguishes the original states. -/
theorem injective_sensor_separates {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (hK : Function.Injective K) {x y : α}
    (h : WordEq K step x y) : x = y :=
  hK (word_now h)

/-- Joint separation by two sensors is sufficient, even if they are
individually non-injective. -/
theorem two_sensors_jointly_separate {α ω ν ι : Type*}
    (K : α → ω) (L : α → ν) (step : ι → α → α)
    (h : ∀ x y, K x = K y → L x = L y → x = y)
    {x y : α}
    (hxy : WordEq (fun a => (K a, L a)) step x y) :
    x = y := by
  have hp := word_now hxy
  exact h x y (congrArg Prod.fst hp) (congrArg Prod.snd hp)

/-- Equality at the initial observation is necessary for every word kernel. -/
theorem any_wordEq_implies_now {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    {x y : α} (h : WordEq K step x y) : K x = K y :=
  word_now h

/-- Equality of original states is sufficient for every observation family. -/
theorem state_eq_implies_bundle {α ω ι δ : Type*}
    (sensor : δ → α → ω) (step : ι → α → α)
    {x y : α} (h : x = y) :
    WordEq (bundle sensor) step x y := by
  subst y
  exact word_refl _ _ _

/-- Sensor postprocessing cannot create new distinctions. -/
theorem bundle_postprocess {α ω ν ι δ : Type*}
    (sensor : δ → α → ω) (post : ω → ν)
    (step : ι → α → α)
    {x y : α} (h : WordEq (bundle sensor) step x y) :
    WordEq (bundle (fun i x => post (sensor i x))) step x y := by
  apply (bundle_wordEq_iff _ step x y).2
  intro i
  exact postprocess (sensor i) post step
    ((bundle_wordEq_iff sensor step x y).1 h i)

/-- A constant-valued sensor is observationally redundant. -/
theorem add_constant_sensor {α ω ν ι : Type*}
    (K : α → ω) (v : ν) (step : ι → α → α)
    (x y : α) :
    WordEq (fun a => (K a, v)) step x y ↔ WordEq K step x y := by
  constructor
  · intro h
    exact ((pair_observation K (fun _ => v) step x y).1 h).1
  · intro h
    exact (pair_observation K (fun _ => v) step x y).2
      ⟨h, by intro word; rfl⟩

/-- An injective postprocessing preserves exactly the sensor's kernel. -/
theorem injective_postprocess_exact {α ω ν ι : Type*}
    (K : α → ω) (post : ω → ν)
    (hinj : Function.Injective post)
    (step : ι → α → α) (x y : α) :
    WordEq (fun a => post (K a)) step x y ↔ WordEq K step x y := by
  constructor
  · intro h word
    exact hinj (h word)
  · exact postprocess K post step

/-- The two coordinate sensors jointly recover all product states. -/
theorem coordinate_bundle_injective {α β : Type*} :
    Function.Injective (fun p : α × β => (p.1,p.2)) := by
  intro x y h
  exact Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- Two coordinate observations completely distinguish any product state,
regardless of the dynamics. -/
theorem coordinates_wordEq_iff_eq {α β ι : Type*}
    (step : ι → (α × β) → (α × β))
    (x y : α × β) :
    WordEq (fun p : α × β => (p.1,p.2)) step x y ↔ x = y := by
  constructor
  · intro h
    exact coordinate_bundle_injective (word_now h)
  · intro h
    subst y
    exact word_refl _ _ _

/-- The first coordinate sensor is not injective on the Bool square. -/
theorem fst_bool_not_injective :
    ¬ Function.Injective (fun p : Bool × Bool => p.1) := by
  intro hinj
  have he : ((false,false) : Bool × Bool) = (false,true) :=
    hinj (by decide)
  have heq : (false : Bool) = true := congrArg Prod.snd he
  cases heq

/-- The second coordinate sensor is not injective on the Bool square. -/
theorem snd_bool_not_injective :
    ¬ Function.Injective (fun p : Bool × Bool => p.2) := by
  intro hinj
  have he : ((false,false) : Bool × Bool) = (true,false) :=
    hinj (by decide)
  have heq : (false : Bool) = true := congrArg Prod.fst he
  cases heq

/-- The paired coordinates are injective despite neither alone being so. -/
theorem bool_pair_jointly_injective :
    Function.Injective (fun p : Bool × Bool => (p.1,p.2)) :=
  coordinate_bundle_injective

end LinearInputOperatorSensors
