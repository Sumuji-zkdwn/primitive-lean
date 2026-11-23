import Std

/-! Observations of the wired square sandpile. A configuration lists grains.
Ghost vertices on the four sides may be erased. The explicit binary harmonic
field below dispenses with any assumption on existence of a harmonic extension.
All results quantify over the side length or the ternary refinement level. -/
namespace SquareClock

abbrev Site := Nat × Nat
abbrev Config := List Site
def interior (M : Nat) (p : Site) : Prop := 0 < p.1 ∧ p.1 < M ∧ 0 < p.2 ∧ p.2 < M
def ghost (M : Nat) (p : Site) : Prop := p.1 = 0 ∨ p.1 = M ∨ p.2 = 0 ∨ p.2 = M
def nbr (p : Site) : Config :=
  [(p.1-1,p.2), (p.1+1,p.2), (p.1,p.2-1), (p.1,p.2+1)]
def wt (p : Site) : Nat := p.1 * p.2
def tally (w : Site → Nat) (s : Config) : Nat := (s.map w).sum
def phase (M : Nat) (s : Config) := tally wt s % M

/-- The q-th coordinate of the discrete Dirichlet field, as a zero-one weight. -/
def field (M q : Nat) (p : Site) : Nat :=
  let (i,j) := p
  if i + j > q ∧ i + q > j ∧ j + q > i ∧ i+j+q < 2*M ∧ (i+j+q)%2 = 1
  then 1 else 0
def bit (M q : Nat) (s : Config) := tally (field M q) s % 2

theorem field_input {M q j : Nat} (hj : 0 < j ∧ j < M) (_hq : 0 < q ∧ q < M) :
    field M q (1,j) = (if q = j then 1 else 0) := by
  simp only [field]
  split <;> split <;> omega

theorem field_sink {M q : Nat} {p : Site} (h : ghost M p) : field M q p = 0 := by
  obtain ⟨i,j⟩ := p
  simp only [ghost] at h
  simp only [field]
  split <;> omega

theorem field_harmonic {M q i j : Nat} (hi : 0 < i ∧ i < M)
    (hj : 0 < j ∧ j < M) (hq : 0 < q ∧ q < M) :
    tally (field M q) (nbr (i,j)) % 2 = 0 := by
  simp only [nbr, tally, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero, field]
  split <;> split <;> split <;> split <;> omega

theorem wt_harmonic {i j : Nat} (hi : 0 < i) (hj : 0 < j) :
    tally wt (nbr (i,j)) = 4 * wt (i,j) := by
  obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  simp [nbr, tally, wt, Nat.succ_mul, Nat.mul_succ] <;> omega

theorem wt_sink {M : Nat} {p : Site} (h : ghost M p) : wt p % M = 0 := by
  obtain ⟨i,j⟩ := p
  rcases h with h|h|h|h <;> simp only at h <;> subst_vars <;> simp [wt]

/-- Four available grains suffice for a legal firing. Permutations permit
selection of any grains. Erasing a boundary grain implements the sink. -/
inductive Step (M : Nat) : Config → Config → Prop
  | perm {s t} (h : List.Perm s t) : Step M s t
  | topple (p : Site) (s : Config) (h : interior M p) :
      Step M (List.replicate 4 p ++ s) (nbr p ++ s)
  | sink (p : Site) (s : Config) (h : ghost M p) : Step M (p :: s) s

inductive Run (M : Nat) : Config → Config → Prop
  | nil (s : Config) : Run M s s
  | next {s t u : Config} (a : Step M s t) (b : Run M t u) : Run M s u

theorem step_preserves {M q : Nat} (hq : 0 < q ∧ q < M) {s t : Config}
    (h : Step M s t) : phase M s = phase M t ∧ bit M q s = bit M q t := by
  cases h with
  | perm hp => exact ⟨congrArg (· % M) ((hp.map wt).sum_nat),
                        congrArg (· % 2) ((hp.map (field M q)).sum_nat)⟩
  | topple p s hp =>
    obtain ⟨i,j⟩ := p
    rcases hp with ⟨hi,hi',hj,hj'⟩
    have hw := wt_harmonic hi hj
    have hb := field_harmonic (And.intro hi hi') (And.intro hj hj') hq
    simp only [phase, bit, tally, List.map_append, List.sum_append_nat,
      List.map_replicate, List.sum_replicate_nat] at *
    constructor
    · rw [hw]
    · apply Nat.add_mod_eq_add_mod_right
      omega
  | sink p s hp =>
    simp only [phase, bit, tally, List.map_cons, List.sum_cons]
    constructor
    · rw [Nat.add_mod, wt_sink hp, Nat.zero_add, Nat.mod_mod]
    · rw [field_sink hp, Nat.zero_add]

theorem run_preserves {M q : Nat} (hq : 0 < q ∧ q < M) {s t : Config}
    (h : Run M s t) : phase M s = phase M t ∧ bit M q s = bit M q t := by
  induction h with
  | nil => exact ⟨rfl,rfl⟩
  | next a _ ih =>
    have ha := step_preserves hq a
    exact ⟨ha.1.trans ih.1, ha.2.trans ih.2⟩

def drive (r j : Nat) (s : Config) : Config := List.replicate r (1,j) ++ s
def period (M j : Nat) := M / M.gcd j

/-- Any legal stabilization of r additions, or indeed any partial relaxation. -/
theorem input_observation {M j q r : Nat} (hj : 0 < j ∧ j < M)
    (hq : 0 < q ∧ q < M) {s t : Config} (h : Run M (drive r j s) t) :
    phase M t = (r*j + tally wt s) % M ∧
    bit M q t = (r*(if q=j then 1 else 0) + tally (field M q) s) % 2 := by
  have ha := run_preserves hq h
  rw [← ha.1, ← ha.2]
  simp [phase, bit, drive, tally, List.sum_replicate_nat,
    wt, field_input hj hq]

private theorem add_mod_cancel_iff {x d M : Nat} :
    (d+x)%M = x%M ↔ M ∣ d := by
  constructor
  · intro h
    obtain ⟨a,b,hab⟩ := Nat.mod_eq_mod_iff.mp h
    have h' : d+a*M = b*M := by omega
    have h'' : M ∣ d+a*M := h' ▸ Nat.dvd_mul_left M b
    have h''' := Nat.dvd_sub h'' (Nat.dvd_mul_left M a)
    simpa using h'''
  · intro h
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd h, Nat.zero_add, Nat.mod_mod]

theorem return_iff {M j r : Nat} (hM : 0 < M) (x : Nat) :
    (r*j+x)%M = x%M ↔ period M j ∣ r := by
  rw [add_mod_cancel_iff, period, Nat.div_dvd_iff_dvd_mul
      (Nat.gcd_dvd_left M j) (Nat.gcd_pos_of_pos_left j hM),
    Nat.dvd_gcd_mul_iff_dvd_mul, Nat.mul_comm]

theorem period_pos {M j : Nat} (hM : 0 < M) : 0 < period M j := by
  apply Nat.div_pos
  · exact Nat.le_of_dvd hM (Nat.gcd_dvd_left M j)
  · exact Nat.gcd_pos_of_pos_left j hM

theorem refine_period (M j : Nat) : period (3*M) (3*j) = period M j := by
  simp only [period, Nat.gcd_mul_left, Nat.mul_div_mul_left _ _ (by decide : 0 < 3)]

theorem fresh_period (m j : Nat) (hj : j%3 ≠ 0) : period (3^m) j = 3^m := by
  have hc : Nat.gcd 3 j = 1 := by
    rw [Nat.gcd_rec 3 j]
    have : j%3 = 1 ∨ j%3 = 2 := by omega
    rcases this with h|h <;> rw [h] <;> decide
  simp [period, Nat.gcd_pow_left_of_gcd_eq_one hc]

theorem period_ternary (m j : Nat) : ∃ k, k ≤ m ∧ period (3^m) j = 3^k := by
  induction m generalizing j with
  | zero => exact ⟨0, by decide, by simp [period]⟩
  | succ m ih =>
    by_cases h : j%3 = 0
    · obtain ⟨v,rfl⟩ := Nat.dvd_of_mod_eq_zero h
      obtain ⟨k,hk,he⟩ := ih v
      exact ⟨k, by omega, by rw [Nat.pow_succ, Nat.mul_comm (3^m) 3, refine_period, he]⟩
    · exact ⟨m+1, Nat.le_refl _, fresh_period _ _ h⟩

theorem square_first_return {m j : Nat} (hj : 0 < j ∧ j < 3^m)
    {s t : Config} (h : Run (3^m) (drive (period (3^m) j) j s) t) :
    phase (3^m) t = phase (3^m) s ∧
    (∀ r, 0 < r → r < period (3^m) j → ∀ u, Run (3^m) (drive r j s) u →
      phase (3^m) u ≠ phase (3^m) s) ∧
    (∀ q, 0 < q ∧ q < 3^m → bit (3^m) q t =
      if q=j then 1 - bit (3^m) q s else bit (3^m) q s) := by
  have hm : 0 < 3^m := Nat.pow_pos (by decide)
  constructor
  · simpa [phase, (return_iff hm (tally wt s)).mpr (Nat.dvd_refl _)] using
      (input_observation hj hj h).1
  constructor
  · intro r hr hlt u hu heq
    rw [(input_observation hj hj hu).1] at heq
    exact (Nat.not_le_of_gt hlt) (Nat.le_of_dvd hr ((return_iff hm _).mp heq))
  · intro q hq
    rw [(input_observation hj hq h).2]
    obtain ⟨k,_,hk⟩ := period_ternary m j
    have odd : (3^k)%2 = 1 := by rw [Nat.pow_mod]; simp
    by_cases e : q=j <;> simp [e, bit, hk] <;> omega

theorem project_phase (r M j : Nat) :
    ((r+3*j)%(3*M))/3 = (r/3+j)%M := by
  rw [Nat.mod_mul_right_div_self]
  congr 1
  omega

def bucket (M P : Nat) := (List.range M).filter fun q => decide (0 < q ∧ period M q = P)
def parityOf (f : Nat → Nat) : List Nat → Nat
  | [] => 0
  | q::tail => (f q + parityOf f tail)%2
def observedBit (M P : Nat) (s : Config) :=
  parityOf (fun q => bit M q s) (bucket M P)

private theorem parityOf_toggle {M j : Nat} {s t : Config}
    (change : ∀ q, 0 < q ∧ q < M → bit M q t =
        if q=j then 1-bit M q s else bit M q s)
    (qs : List Nat) (hn : qs.Nodup) (valid : ∀ q ∈ qs, 0 < q ∧ q < M) :
    parityOf (fun q => bit M q t) qs =
    ((if j ∈ qs then 1 else 0) + parityOf (fun q => bit M q s) qs)%2 := by
  induction qs with
  | nil => simp [parityOf]
  | cons q tail ih =>
    rcases List.nodup_cons.mp hn with ⟨hn,ht⟩
    have tailEq := ih ht (fun v hv => valid v (List.mem_cons_of_mem _ hv))
    have headEq := change q (valid q (by simp))
    have hh : bit M q s < 2 := Nat.mod_lt _ (by decide)
    by_cases eq : q=j
    · subst q
      simp [parityOf, tailEq, headEq, hn]
      omega
    · by_cases inside : j ∈ tail <;>
        simp [parityOf, tailEq, headEq, eq, Ne.symm eq, inside] <;> omega

theorem switched_bucket {m j : Nat} (hj : 0 < j ∧ j < 3^m) {s t : Config}
    (h : Run (3^m) (drive (period (3^m) j) j s) t) (P : Nat) :
    observedBit (3^m) P t = ((if period (3^m) j = P then 1 else 0) +
      observedBit (3^m) P s)%2 := by
  have hq : ∀ q ∈ bucket (3^m) P, 0 < q ∧ q < 3^m := by
    intro q hq
    simp [bucket] at hq
    exact ⟨hq.2.1,hq.1⟩
  have hn : (bucket (3^m) P).Nodup := List.nodup_range.filter _
  have eq := parityOf_toggle (square_first_return hj h).2.2 _ hn hq
  simpa [observedBit, bucket, hj.1, hj.2] using eq

/-- A Lyapunov weight for a grain. A firing decreases the total by four;
discarding a ghost decreases it by at least one. -/
def potential1 (M i : Nat) := i*(M-i)
def weight (M : Nat) (p : Site) := 1 + potential1 M p.1 + potential1 M p.2

private theorem potential1_lap {M i : Nat} (hi : 0<i ∧ i<M) :
    potential1 M (i-1) + potential1 M (i+1) + 2 = 2*potential1 M i := by
  obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i≠0)
  obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le (show a+2 ≤ M by omega)
  simp only [potential1, Nat.succ_sub_one, Nat.succ_eq_add_one]
  have e1 : a+2+b-a = b+2 := by omega
  have e2 : a+2+b-(a+1+1) = b := by omega
  have e3 : a+2+b-(a+1) = b+1 := by omega
  simp only [e1,e2,e3,Nat.mul_add,Nat.add_mul,Nat.one_mul,Nat.mul_one]
  omega

private theorem potential_lap {M : Nat} {p : Site} (hi : interior M p) :
    tally (weight M) (nbr p) + 4 = 4*weight M p := by
  obtain ⟨i,j⟩ := p
  rcases hi with ⟨hi,hi',hj,hj'⟩
  have hx := potential1_lap (And.intro hi hi')
  have hy := potential1_lap (And.intro hj hj')
  dsimp only at hx hy
  simp [nbr,tally,weight]
  omega

/-- These are precisely the two possible physical moves up to listing order. -/
inductive Move (M : Nat) : Config → Config → Prop
  | topple {s : Config} (p : Site) (rest : Config)
      (available : s.Perm (List.replicate 4 p ++ rest)) (hp : interior M p) :
      Move M s (nbr p ++ rest)
  | sink {s : Config} (p : Site) (rest : Config)
      (available : s.Perm (p::rest)) (hp : ghost M p) : Move M s rest

def stable (M : Nat) (s : Config) := ∀ t, ¬Move M s t

theorem exists_stabilization (M : Nat) (s : Config) :
    ∃ t, Run M s t ∧ stable M t := by
  induction s using (measure (tally (weight M))).wf.induction with
  | h s ih =>
    by_cases hs : stable M s
    · exact ⟨s, .nil s, hs⟩
    · have hex : ∃ t, Move M s t := by
        apply Classical.byContradiction
        intro no
        exact hs (fun t ht => no ⟨t,ht⟩)
      obtain ⟨t,ht⟩ := hex
      cases ht with
      | topple p rest avail hp =>
        have he := (avail.map (weight M)).sum_nat
        have hl := potential_lap hp
        have dec : tally (weight M) (nbr p ++ rest) < tally (weight M) s := by
          simp only [tally, List.map_append, List.sum_append_nat, List.map_replicate,
            List.sum_replicate_nat] at *
          omega
        obtain ⟨v,hv,stableV⟩ := ih _ dec
        exact ⟨v,.next (.perm avail) (.next (.topple p rest hp) hv),stableV⟩
      | sink p rest avail hp =>
        have he := (avail.map (weight M)).sum_nat
        have dec : tally (weight M) t < tally (weight M) s := by
          simp only [tally, List.map_cons, List.sum_cons] at *
          rw [he]
          simp only [weight]
          omega
        obtain ⟨v,hv,stableV⟩ := ih _ dec
        exact ⟨v,.next (.perm avail) (.next (.sink p t hp) hv),stableV⟩

theorem Run.trans {M s t u} (a : Run M s t) (b : Run M t u) : Run M s u := by
  induction a with
  | nil => exact b
  | next step _ ih => exact .next step (ih b)

private theorem frame_step {M s t} (p : Site) (a : Step M s t) :
    Run M (p::s) (p::t) := by
  cases a with
  | perm h => exact .next (.perm (h.cons p)) (.nil _)
  | topple q rest h =>
    exact .next (.perm List.perm_middle.symm)
      (.next (.topple q (p::rest) h) (.next (.perm List.perm_middle) (.nil _)))
  | sink q rest h =>
    exact .next (.perm (List.Perm.swap q p t)) (.next (.sink q (p::t) h) (.nil _))

private theorem frame_run {M s t} (p : Site) (a : Run M s t) :
    Run M (p::s) (p::t) := by
  induction a with
  | nil => exact .nil _
  | next step _ ih => exact (frame_step p step).trans ih

/-- Add a single grain and stabilize fully before the next input. -/
inductive Inputs (M j : Nat) : Nat → Config → Config → Prop
  | nil (s) : Inputs M j 0 s s
  | add {k s u t} (previous : Inputs M j k s u)
      (step : Run M ((1,j)::u) t) (settled : stable M t) : Inputs M j (k+1) s t

theorem inputs_exist (M j r : Nat) (s : Config) : ∃ t, Inputs M j r s t := by
  induction r with
  | zero => exact ⟨s,.nil s⟩
  | succ n ih =>
    obtain ⟨u,h⟩ := ih
    obtain ⟨t,step,settled⟩ := exists_stabilization M ((1,j)::u)
    exact ⟨t,.add h step settled⟩

theorem inputs_bulk {M j r : Nat} {s t : Config} (h : Inputs M j r s t) :
    Run M (drive r j s) t := by
  induction h with
  | nil s => simpa [drive] using Run.nil (M:=M) s
  | add _ step _ ih =>
    simpa [drive, List.replicate_succ] using (frame_run (1,j) ih).trans step

/-- The physical first-return gate, for every initial configuration and every
ternary stage. Every bit here is the parity of actual grain positions in the
explicit family of harmonic fields. The conclusion includes existence of an
actual one-at-a-time input trajectory with a stabilization after every grain. -/
theorem sandpile_gate {m j : Nat} (hj : 0 < j ∧ j < 3^m) (s : Config) :
    (∃ t, Inputs (3^m) j (period (3^m) j) s t) ∧
    (∀ r, 0 < r → r < period (3^m) j → ∀ u, Inputs (3^m) j r s u →
      phase (3^m) u ≠ phase (3^m) s) ∧
    (∀ t, Inputs (3^m) j (period (3^m) j) s t →
      phase (3^m) t = phase (3^m) s ∧
      ∀ P, observedBit (3^m) P t =
        ((if period (3^m) j = P then 1 else 0) + observedBit (3^m) P s)%2) ∧
    (∃ k, k ≤ m ∧ period (3^m) j = 3^k) ∧
    period (3*(3^m)) (3*j) = period (3^m) j ∧
    (∀ r, ((r+3*j)%(3*(3^m)))/3 = (r/3+j)%(3^m)) := by
  obtain ⟨t,hit⟩ := inputs_exist (3^m) j (period (3^m) j) s
  exact ⟨⟨t,hit⟩, fun r hr hlt u hu =>
    (square_first_return hj (inputs_bulk hit)).2.1 r hr hlt u (inputs_bulk hu),
    fun _ h => ⟨(square_first_return hj (inputs_bulk h)).1,
      switched_bucket hj (inputs_bulk h)⟩, period_ternary m j, refine_period _ _,
    fun r => project_phase r _ _⟩

/-! A circular coordinate on the same state space. Its two orientations and all
gate changes are physical boundary input protocols on a single square. -/
def angle (M : Nat) (s : Config) := ((M+1)/2 * phase M s)%M

private theorem parityOf_congr_on {f g : Nat → Nat} (qs : List Nat)
    (h : ∀ q ∈ qs, f q = g q) : parityOf f qs = parityOf g qs := by
  induction qs with
  | nil => rfl
  | cons q tail ih =>
    rw [parityOf, parityOf, h q (by simp),
      ih (fun a ha => h a (List.mem_cons_of_mem q ha))]

/-- Two grains at j preserve every bucket and rotate the normalized angle by j. -/
theorem two_inputs {m j : Nat} (hj : 0<j ∧ j<3^m) {s t : Config}
    (h : Inputs (3^m) j 2 s t) :
    angle (3^m) t = (angle (3^m) s + j)%(3^m) ∧
    ∀ P, observedBit (3^m) P t = observedBit (3^m) P s := by
  let M := 3^m
  let D := (M+1)/2
  have odd : M%2=1 := by dsimp [M]; rw [Nat.pow_mod]; simp
  have double : D*2 = M+1 := by dsimp [D]; omega
  constructor
  · have ha := (input_observation hj hj (inputs_bulk h)).1
    change (D*phase M t)%M = ((D*phase M s)%M + j)%M
    change phase M t = (2*j + tally wt s)%M at ha
    rw [ha, Nat.mul_mod_mod, Nat.mod_add_mod]
    change _ = (D*(tally wt s%M)+j)%M
    rw [Nat.mul_add, ← Nat.mul_assoc, double, Nat.add_mul, Nat.one_mul]
    calc
      _ = (M*j+(D*tally wt s+j))%M := by congr 1; omega
      _ = (D*tally wt s+j)%M := Nat.mul_add_mod_self_left _ _ _
      _ = _ := by
        apply Nat.add_mod_eq_add_mod_right
        simp
  · intro P
    apply parityOf_congr_on
    intro q hq
    simp [bucket] at hq
    have hb := (input_observation hj ⟨hq.2.1,hq.1⟩ (inputs_bulk h)).2
    rw [hb]
    by_cases e : q=j <;> simp [e,bit] <;> omega

private theorem angle_gate {m j : Nat} (hj : 0<j ∧ j<3^m) {s t : Config}
    (h : Inputs (3^m) j (period (3^m) j) s t) :
    angle (3^m) t = angle (3^m) s := by
  unfold angle
  rw [(square_first_return hj (inputs_bulk h)).1]

/-- Allowed endpoint pairs of a finite succession of physical protocols. -/
inductive Motion (m : Nat) : Config → Config → Prop
  | stay (s) : Motion m s s
  | rotate {s t u} (past : Motion m s t) (step : Inputs (3^m) 1 2 t u) : Motion m s u
  | back {s t u} (past : Motion m s t) (step : Inputs (3^m) (3^m-1) 2 t u) : Motion m s u
  | gate {s t u j} (past : Motion m s t) (port : 0<j ∧ j<3^m)
      (step : Inputs (3^m) j (period (3^m) j) t u) : Motion m s u

private theorem ternary_port (k l : Nat) :
    period (3^(k+l)) (3^l) = 3^k := by
  induction l with
  | zero => simpa using (fresh_period k 1 (by decide))
  | succ l ih =>
    rw [Nat.add_succ, Nat.pow_succ, Nat.pow_succ 3 l,
      Nat.mul_comm _ 3, Nat.mul_comm (3^l) 3, refine_period, ih]

private theorem parityOf_lt (f : Nat→Nat) (qs : List Nat) : parityOf f qs < 2 := by
  cases qs with
  | nil => simp [parityOf]
  | cons => exact Nat.mod_lt _ (by decide)

private theorem set_prefix {m : Nat} (s : Config) (f : Nat → Fin 2) (n : Nat) (hn : n≤m) :
    ∃ t, Motion m s t ∧ angle (3^m) t = angle (3^m) s ∧
      ∀ k, 0<k → k≤n → observedBit (3^m) (3^k) t = (f k).val := by
  induction n with
  | zero => exact ⟨s, .stay _, rfl, fun _ hk h => by omega⟩
  | succ n ih =>
    obtain ⟨t,past,hang,hbits⟩ := ih (by omega)
    let k := n+1
    by_cases ok : observedBit (3^m) (3^k) t = (f k).val
    · refine ⟨t,past,hang,?_⟩
      intro a ha hb
      by_cases e : a=k
      · simpa [e] using ok
      · apply hbits a ha
        dsimp [k] at e; omega
    · let l := m-k
      have em : k+l=m := by dsimp [k,l]; omega
      have hl : l<m := by dsimp [k,l]; omega
      let j := 3^l
      have hj : 0<j ∧ j<3^m :=
        ⟨Nat.pow_pos (by decide), Nat.pow_lt_pow_right (by decide) hl⟩
      have hp : period (3^m) j = 3^k := em ▸ ternary_port k l
      obtain ⟨u,step⟩ := inputs_exist (3^m) j (period (3^m) j) t
      refine ⟨u, .gate past hj step, (angle_gate hj step).trans hang, ?_⟩
      intro a ha hb
      rw [switched_bucket hj (inputs_bulk step), hp]
      by_cases ea : a=k
      · subst a
        have small : observedBit (3^m) (3^k) t < 2 := parityOf_lt _ _
        have goal_small := (f k).isLt
        simp; omega
      · have ep : 3^k ≠ 3^a := by
          intro e
          exact ea ((Nat.pow_right_inj (by decide : 1<3)).mp e).symm
        have bound : a≤n := by dsimp [k] at ea; omega
        simp [ep, hbits a ha bound]

private theorem rotate_many {m : Nat} (hm : 1<3^m) {s t : Config} (past : Motion m s t)
    (r : Nat) : ∃ u, Motion m s u ∧ angle (3^m) u = (angle (3^m) t+r)%(3^m) ∧
      ∀ P, observedBit (3^m) P u = observedBit (3^m) P t := by
  induction r with
  | zero =>
    refine ⟨t,past,?_,fun _ => rfl⟩
    simp [angle]
  | succ r ih =>
    obtain ⟨u,past,hu,hbits⟩ := ih
    obtain ⟨v,step⟩ := inputs_exist (3^m) 1 2 u
    have hs := two_inputs ⟨by decide,hm⟩ step
    refine ⟨v,.rotate past step,?_,fun P => (hs.2 P).trans (hbits P)⟩
    rw [hs.1, hu, Nat.mod_add_mod, Nat.add_assoc]

/-- Surjectivity of the joint observable on the physical orbit of each
initial state (including any recurrent state). -/
theorem joint_reachable {m : Nat} (hm : 1<3^m) (s : Config) (a : Fin (3^m))
    (f : Nat → Fin 2) : ∃ t, Motion m s t ∧ angle (3^m) t = a.val ∧
      ∀ k, 0<k → k≤m → observedBit (3^m) (3^k) t = (f k).val := by
  obtain ⟨t,past,_,hbits⟩ := set_prefix s f m (Nat.le_refl _)
  obtain ⟨u,steps,hu,keep⟩ := rotate_many hm past ((3^m-angle (3^m) t)+a.val)
  refine ⟨u,steps,?_,fun k hk hb => (keep _).trans (hbits k hk hb)⟩
  have hlt : angle (3^m) t < 3^m := Nat.mod_lt _ (by omega)
  have eq : angle (3^m) t + (3^m-angle (3^m) t+a.val) = 3^m+a.val := by omega
  rw [hu, eq, Nat.add_mod_left, Nat.mod_eq_of_lt a.isLt]

theorem square_phase_and_gate {m j : Nat} (hj : 0<j ∧ j<3^m) (s : Config) :
    (∀ t, Inputs (3^m) 1 2 s t → angle (3^m) t = (angle (3^m) s+1)%(3^m) ∧
      ∀ P, observedBit (3^m) P t = observedBit (3^m) P s) ∧
    (∀ t, Inputs (3^m) (3^m-1) 2 s t →
      angle (3^m) t = (angle (3^m) s+(3^m-1))%(3^m) ∧
      ∀ P, observedBit (3^m) P t = observedBit (3^m) P s) ∧
    (∀ t, Inputs (3^m) j (period (3^m) j) s t →
      angle (3^m) t = angle (3^m) s ∧ ∀ P, observedBit (3^m) P t =
        ((if period (3^m) j = P then 1 else 0) + observedBit (3^m) P s)%2) ∧
    (∀ a : Fin (3^m), ∀ f : Nat → Fin 2, ∃ t, Motion m s t ∧ angle (3^m) t = a.val ∧
      ∀ k, 0<k → k≤m → observedBit (3^m) (3^k) t = (f k).val) := by
  have side : 1<3^m := by omega
  exact ⟨fun _ h => two_inputs ⟨by decide,side⟩ h,
    fun _ h => two_inputs ⟨by omega, by omega⟩ h,
    fun _ h => ⟨angle_gate hj h, switched_bucket hj (inputs_bulk h)⟩,
    joint_reachable side s⟩

/-- Interchanging a two-grain rotation and a gate return preserves the joint
observable. Nothing in this statement identifies the underlying configurations. -/
theorem observed_commute {m j i : Nat} (hj : 0<j ∧ j<3^m) (hi : 0<i ∧ i<3^m)
    {s a b c d : Config} (sa : Inputs (3^m) i 2 s a)
    (ab : Inputs (3^m) j (period (3^m) j) a b)
    (sc : Inputs (3^m) j (period (3^m) j) s c) (cd : Inputs (3^m) i 2 c d) :
    angle (3^m) b = angle (3^m) d ∧
    ∀ P, observedBit (3^m) P b = observedBit (3^m) P d := by
  constructor
  · rw [angle_gate hj ab, (two_inputs hi sa).1, (two_inputs hi cd).1, angle_gate hj sc]
  · intro P
    rw [switched_bucket hj (inputs_bulk ab), (two_inputs hi sa).2,
      (two_inputs hi cd).2, switched_bucket hj (inputs_bulk sc)]

end SquareClock
