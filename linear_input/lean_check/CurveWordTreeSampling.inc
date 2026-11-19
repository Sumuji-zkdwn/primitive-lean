/-!
Finite height-level sampling of a continuous height-coded path.  Hitting
times below are actual extrema of compact level sets, not additional
existence hypotheses on the path.
-/

noncomputable section

namespace LinearInputCurveWordTreeSampling

open Set
open LinearInputCurveWordSignatureTree LinearInputCurveWordTreeSignature
open LinearInputCurveWordHeightMetric LinearInputCurveWordSamplingOrder

def hitSet (h : ℝ → ℝ) (s t c : ℝ) : Set ℝ := Icc s t ∩ h ⁻¹' {c}

theorem hitSet_compact {h : ℝ → ℝ} {s t : ℝ}
    (hh : ContinuousOn h (Icc s t)) (c : ℝ) : IsCompact (hitSet h s t c) :=
  isCompact_Icc.of_isClosed_subset
    (hh.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left

theorem hitSet_nonempty {h : ℝ → ℝ} {s t c : ℝ} (hst : s ≤ t)
    (hh : ContinuousOn h (Icc s t)) (hc : c ∈ uIcc (h s) (h t)) :
    (hitSet h s t c).Nonempty := by
  obtain ⟨r, hr, he⟩ := intermediate_value_uIcc
    (by simpa only [uIcc_of_le hst] using hh) hc
  exact ⟨r, by simpa only [hitSet, mem_inter_iff, Set.mem_preimage,
    mem_singleton_iff, uIcc_of_le hst] using And.intro hr he⟩

def firstHit (h : ℝ → ℝ) (s t c : ℝ) : ℝ := sInf (hitSet h s t c)

def lastHit (h : ℝ → ℝ) (s t c : ℝ) : ℝ := sSup (hitSet h s t c)

theorem firstHit_spec {h : ℝ → ℝ} {s t c : ℝ} (hst : s ≤ t)
    (hh : ContinuousOn h (Icc s t)) (hc : c ∈ uIcc (h s) (h t)) :
    firstHit h s t c ∈ Icc s t ∧ h (firstHit h s t c) = c ∧
      ∀r ∈ Icc s t, h r = c → firstHit h s t c ≤ r := by
  have he := (hitSet_compact hh c).isLeast_sInf (hitSet_nonempty hst hh hc)
  exact ⟨he.1.1, he.1.2, fun r hr heq => he.2 ⟨hr, heq⟩⟩

theorem lastHit_spec {h : ℝ → ℝ} {s t c : ℝ} (hst : s ≤ t)
    (hh : ContinuousOn h (Icc s t)) (hc : c ∈ uIcc (h s) (h t)) :
    lastHit h s t c ∈ Icc s t ∧ h (lastHit h s t c) = c ∧
      ∀r ∈ Icc s t, h r = c → r ≤ lastHit h s t c := by
  have he := (hitSet_compact hh c).isGreatest_sSup (hitSet_nonempty hst hh hc)
  exact ⟨he.1.1, he.1.2, fun r hr heq => he.2 ⟨hr, heq⟩⟩

theorem firstHit_left {h : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hh : ContinuousOn h (Icc s t)) : firstHit h s t (h s) = s := by
  have he := firstHit_spec hst hh (c := h s) left_mem_uIcc
  exact le_antisymm (he.2.2 s (left_mem_Icc.mpr hst) rfl) he.1.1

theorem lastHit_right {h : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hh : ContinuousOn h (Icc s t)) : lastHit h s t (h t) = t := by
  have he := lastHit_spec hst hh (c := h t) right_mem_uIcc
  exact le_antisymm he.1.2 (he.2.2 t (right_mem_Icc.mpr hst) rfl)

/-- Before the first downward crossing of a level the height cannot lie
below that level. -/
theorem le_height_before_firstHit {h : ℝ → ℝ} {s t c : ℝ} (hst : s ≤ t)
    (hh : ContinuousOn h (Icc s t)) (hc : h t ≤ c ∧ c ≤ h s)
    {r : ℝ} (hr : r ∈ Icc s (firstHit h s t c)) : c ≤ h r := by
  have hspec := firstHit_spec hst hh (c := c) (by
    exact ⟨le_trans (min_le_right _ _) hc.1,
      le_trans hc.2 (le_max_left _ _)⟩)
  by_contra hn
  have hlt : h r < c := lt_of_not_ge hn
  have hrt : r ≤ t := le_trans hr.2 hspec.1.2
  obtain ⟨q, hq, he⟩ := intermediate_value_Icc' hr.1
    (hh.mono (Icc_subset_Icc le_rfl hrt)) ⟨le_of_lt hlt, hc.2⟩
  have hl := hspec.2.2 q ⟨hq.1, le_trans hq.2 hrt⟩ he
  have hqr : q = r := le_antisymm hq.2 (le_trans hr.2 hl)
  exact (ne_of_lt hlt) (by simpa only [hqr] using he)

/-- After the last upward crossing, the height remains at least the
crossed level. -/
theorem le_height_after_lastHit {h : ℝ → ℝ} {s t c : ℝ} (hst : s ≤ t)
    (hh : ContinuousOn h (Icc s t)) (hc : h s ≤ c ∧ c ≤ h t)
    {r : ℝ} (hr : r ∈ Icc (lastHit h s t c) t) : c ≤ h r := by
  have hspec := lastHit_spec hst hh (c := c)
    ⟨le_trans (min_le_left _ _) hc.1, le_trans hc.2 (le_max_right _ _)⟩
  by_contra hn
  have hlt : h r < c := lt_of_not_ge hn
  have hsr : s ≤ r := le_trans hspec.1.1 hr.1
  obtain ⟨q, hq, he⟩ := intermediate_value_Icc hr.2
    (hh.mono (Icc_subset_Icc hsr le_rfl)) ⟨le_of_lt hlt, hc.2⟩
  have hl := hspec.2.2 q ⟨le_trans hsr hq.1, hq.2⟩ he
  have hqr : q = r := le_antisymm (le_trans hl hr.1) hq.1
  exact (ne_of_lt hlt) (by simpa only [hqr] using he)

theorem firstHit_strictAnti {h : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hh : ContinuousOn h (Icc s t)) :
    StrictAntiOn (firstHit h s t) (Icc (h t) (h s)) := by
  intro c hc d hd hcd
  have sc := firstHit_spec hst hh (c := c)
    ⟨le_trans (min_le_right _ _) hc.1, le_trans hc.2 (le_max_left _ _)⟩
  have sd := firstHit_spec hst hh (c := d)
    ⟨le_trans (min_le_right _ _) hd.1, le_trans hd.2 (le_max_left _ _)⟩
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc' sc.1.1
    (hh.mono (Icc_subset_Icc le_rfl sc.1.2))
    (show d ∈ Icc (h (firstHit h s t c)) (h s) by rw [sc.2.1]; exact ⟨hcd.le, hd.2⟩)
  have hle := le_trans (sd.2.2 r ⟨hr.1, le_trans hr.2 sc.1.2⟩ he) hr.2
  exact lt_of_le_of_ne hle (fun heq => (ne_of_lt hcd) (by
    rw [← sc.2.1, ← sd.2.1, heq]))

theorem lastHit_strictMono {h : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hh : ContinuousOn h (Icc s t)) :
    StrictMonoOn (lastHit h s t) (Icc (h s) (h t)) := by
  intro c hc d hd hcd
  have sc := lastHit_spec hst hh (c := c)
    ⟨le_trans (min_le_left _ _) hc.1, le_trans hc.2 (le_max_right _ _)⟩
  have sd := lastHit_spec hst hh (c := d)
    ⟨le_trans (min_le_left _ _) hd.1, le_trans hd.2 (le_max_right _ _)⟩
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc sc.1.2
    (hh.mono (Icc_subset_Icc sc.1.1 le_rfl))
    (show d ∈ Icc (h (lastHit h s t c)) (h t) by rw [sc.2.1]; exact ⟨hcd.le, hd.2⟩)
  have hle := le_trans hr.1 (sd.2.2 r ⟨le_trans sc.1.1 hr.1, hr.2⟩ he)
  exact lt_of_le_of_ne hle (fun heq => (ne_of_lt hcd) (by
    rw [← sc.2.1, ← sd.2.1, heq]))

/-- Two sampled times are joined at consecutive selected height levels,
and the intervening path never goes below the lower endpoint height. -/
def HeightStep (h : ℝ → ℝ) (L : Finset ℝ) (x y : ℝ) : Prop :=
  h x ∈ L ∧ h y ∈ L ∧
  (∀r ∈ Icc x y, min (h x) (h y) ≤ h r) ∧
  ∀c ∈ L, ¬(min (h x) (h y) < c ∧ c < max (h x) (h y))

def descendingSet (h : ℝ → ℝ) (L : Finset ℝ) (s t : ℝ) : Finset ℝ :=
  insert t ((L.filter (fun c => h t ≤ c ∧ c ≤ h s)).image (firstHit h s t))

def ascendingSet (h : ℝ → ℝ) (L : Finset ℝ) (s t : ℝ) : Finset ℝ :=
  insert s ((L.filter (fun c => h s ≤ c ∧ c ≤ h t)).image (lastHit h s t))

theorem descendingSet_spec {h : ℝ → ℝ} {L : Finset ℝ} {s t : ℝ}
    (hst : s ≤ t) (hh : ContinuousOn h (Icc s t))
    (htL : h t ∈ L) (hts : h t ≤ h s) {x : ℝ}
    (hx : x ∈ descendingSet h L s t) :
    x ∈ Icc s t ∧ h x ∈ L ∧ h x ∈ Icc (h t) (h s) ∧
      firstHit h s t (h x) ≤ x ∧ (x < t → firstHit h s t (h x) = x) := by
  classical
  rcases Finset.mem_insert.mp hx with hxt | hx
  · subst x
    have he := firstHit_spec hst hh (c := h t) right_mem_uIcc
    exact ⟨right_mem_Icc.mpr hst, htL, ⟨le_rfl, hts⟩, he.1.2,
      fun hn => False.elim (lt_irrefl _ hn)⟩
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hcL, hc⟩ := Finset.mem_filter.mp hc
    have he := firstHit_spec hst hh (c := c)
      ⟨le_trans (min_le_right _ _) hc.1, le_trans hc.2 (le_max_left _ _)⟩
    refine ⟨he.1, ?_, ?_, ?_, ?_⟩ <;> simp only [he.2.1]
    · exact hcL
    · exact hc
    · exact le_rfl
    · intro _; trivial

theorem descendingSet_endpoints {h : ℝ → ℝ} {L : Finset ℝ} {s t : ℝ}
    (hst : s ≤ t) (hh : ContinuousOn h (Icc s t))
    (hsL : h s ∈ L) (hts : h t ≤ h s) :
    s ∈ descendingSet h L s t ∧ t ∈ descendingSet h L s t := by
  classical
  refine ⟨Finset.mem_insert_of_mem ?_, Finset.mem_insert_self _ _⟩
  exact Finset.mem_image.mpr ⟨h s, Finset.mem_filter.mpr ⟨hsL, hts, le_rfl⟩,
    firstHit_left hst hh⟩

theorem descendingSet_step {h : ℝ → ℝ} {L : Finset ℝ} {s t : ℝ}
    (hst : s ≤ t) (hh : ContinuousOn h (Icc s t)) (htL : h t ∈ L)
    (hmin : ∀r ∈ Icc s t, h t ≤ h r) {x y : ℝ}
    (hx : x ∈ descendingSet h L s t) (hy : y ∈ descendingSet h L s t)
    (hxy : x < y)
    (hcon : ∀z ∈ descendingSet h L s t, x < z → y ≤ z) : HeightStep h L x y := by
  classical
  have hts := hmin s (left_mem_Icc.mpr hst)
  have sx := descendingSet_spec hst hh htL hts hx
  have sy := descendingSet_spec hst hh htL hts hy
  have ex := sx.2.2.2.2 (lt_of_lt_of_le hxy sy.1.2)
  have hle : h y ≤ h x := by
    by_contra hn
    have hlt := lt_of_not_ge hn
    have hyt : y < t := lt_of_le_of_ne sy.1.2 (fun he => by
      have hhx := sx.2.2.1.1
      rw [he] at hlt
      exact not_lt_of_ge hhx hlt)
    have hhits := firstHit_strictAnti hst hh sx.2.2.1 sy.2.2.1 hlt
    rw [ex, sy.2.2.2.2 hyt] at hhits
    exact lt_asymm hxy hhits
  refine ⟨sx.2.1, sy.2.1, ?_, ?_⟩
  · intro r hr
    rw [min_eq_right hle]
    by_cases hyt : y = t
    · rw [hyt]
      exact hmin r ⟨le_trans sx.1.1 hr.1, le_trans hr.2 sy.1.2⟩
    · have ey := sy.2.2.2.2 (lt_of_le_of_ne sy.1.2 hyt)
      exact le_height_before_firstHit hst hh sy.2.2.1
        ⟨le_trans sx.1.1 hr.1, by simpa only [ey] using hr.2⟩
  · intro c hcL hc
    rw [min_eq_right hle, max_eq_left hle] at hc
    have hcI : c ∈ Icc (h t) (h s) :=
      ⟨le_trans sy.2.2.1.1 hc.1.le, le_trans hc.2.le sx.2.2.1.2⟩
    have hxc : x < firstHit h s t c := by
      simpa only [ex] using firstHit_strictAnti hst hh hcI sx.2.2.1 hc.2
    have hcy : firstHit h s t c < y :=
      lt_of_lt_of_le (firstHit_strictAnti hst hh sy.2.2.1 hcI hc.1) sy.2.2.2.1
    have hm : firstHit h s t c ∈ descendingSet h L s t :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨c, Finset.mem_filter.mpr ⟨hcL, hcI⟩, rfl⟩)
    exact not_lt_of_ge (hcon _ hm hxc) hcy

theorem ascendingSet_spec {h : ℝ → ℝ} {L : Finset ℝ} {s t : ℝ}
    (hst : s ≤ t) (hh : ContinuousOn h (Icc s t))
    (hsL : h s ∈ L) (hst' : h s ≤ h t) {x : ℝ}
    (hx : x ∈ ascendingSet h L s t) :
    x ∈ Icc s t ∧ h x ∈ L ∧ h x ∈ Icc (h s) (h t) ∧
      x ≤ lastHit h s t (h x) ∧ (s < x → lastHit h s t (h x) = x) := by
  classical
  rcases Finset.mem_insert.mp hx with hxt | hx
  · subst x
    have he := lastHit_spec hst hh (c := h s) left_mem_uIcc
    exact ⟨left_mem_Icc.mpr hst, hsL, ⟨le_rfl, hst'⟩, he.1.1,
      fun hn => False.elim (lt_irrefl _ hn)⟩
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hcL, hc⟩ := Finset.mem_filter.mp hc
    have he := lastHit_spec hst hh (c := c)
      ⟨le_trans (min_le_left _ _) hc.1, le_trans hc.2 (le_max_right _ _)⟩
    refine ⟨he.1, ?_, ?_, ?_, ?_⟩ <;> simp only [he.2.1]
    · exact hcL
    · exact hc
    · exact le_rfl
    · intro _; trivial

theorem ascendingSet_endpoints {h : ℝ → ℝ} {L : Finset ℝ} {s t : ℝ}
    (hst : s ≤ t) (hh : ContinuousOn h (Icc s t))
    (htL : h t ∈ L) (hst' : h s ≤ h t) :
    s ∈ ascendingSet h L s t ∧ t ∈ ascendingSet h L s t := by
  classical
  refine ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem ?_⟩
  exact Finset.mem_image.mpr ⟨h t, Finset.mem_filter.mpr ⟨htL, hst', le_rfl⟩,
    lastHit_right hst hh⟩

theorem ascendingSet_step {h : ℝ → ℝ} {L : Finset ℝ} {s t : ℝ}
    (hst : s ≤ t) (hh : ContinuousOn h (Icc s t)) (hsL : h s ∈ L)
    (hmin : ∀r ∈ Icc s t, h s ≤ h r) {x y : ℝ}
    (hx : x ∈ ascendingSet h L s t) (hy : y ∈ ascendingSet h L s t)
    (hxy : x < y)
    (hcon : ∀z ∈ ascendingSet h L s t, x < z → y ≤ z) : HeightStep h L x y := by
  classical
  have hst' := hmin t (right_mem_Icc.mpr hst)
  have sx := ascendingSet_spec hst hh hsL hst' hx
  have sy := ascendingSet_spec hst hh hsL hst' hy
  have ey := sy.2.2.2.2 (lt_of_le_of_lt sx.1.1 hxy)
  have hle : h x ≤ h y := by
    by_contra hn
    have hlt := lt_of_not_ge hn
    have hsx : s < x := lt_of_le_of_ne sx.1.1 (fun he => by
      have hhy := sy.2.2.1.1
      rw [← he] at hlt
      exact not_lt_of_ge hhy hlt)
    have hhits := lastHit_strictMono hst hh sy.2.2.1 sx.2.2.1 hlt
    rw [ey, sx.2.2.2.2 hsx] at hhits
    exact lt_asymm hxy hhits
  refine ⟨sx.2.1, sy.2.1, ?_, ?_⟩
  · intro r hr
    rw [min_eq_left hle]
    by_cases hsx : s = x
    · rw [← hsx]
      exact hmin r ⟨le_trans sx.1.1 hr.1, le_trans hr.2 sy.1.2⟩
    · have ex := sx.2.2.2.2 (lt_of_le_of_ne sx.1.1 hsx)
      exact le_height_after_lastHit hst hh sx.2.2.1
        ⟨by simpa only [ex] using hr.1, le_trans hr.2 sy.1.2⟩
  · intro c hcL hc
    rw [min_eq_left hle, max_eq_right hle] at hc
    have hcI : c ∈ Icc (h s) (h t) :=
      ⟨le_trans sx.2.2.1.1 hc.1.le, le_trans hc.2.le sy.2.2.1.2⟩
    have hxc : x < lastHit h s t c :=
      lt_of_le_of_lt sx.2.2.2.1 (lastHit_strictMono hst hh sx.2.2.1 hcI hc.1)
    have hcy : lastHit h s t c < y := by
      simpa only [ey] using lastHit_strictMono hst hh hcI sy.2.2.1 hc.2
    have hm : lastHit h s t c ∈ ascendingSet h L s t :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨c, Finset.mem_filter.mpr ⟨hcL, hcI⟩, rfl⟩)
    exact not_lt_of_ge (hcon _ hm hxc) hcy

theorem descendingSet_good {h : ℝ → ℝ} {L : Finset ℝ} {s t : ℝ}
    (hst : s ≤ t) (hh : ContinuousOn h (Icc s t)) (hsL : h s ∈ L) (htL : h t ∈ L)
    (hmin : ∀r ∈ Icc s t, h t ≤ h r) :
    GoodSampling (HeightStep h L) s t (descendingSet h L s t) := by
  have he := descendingSet_endpoints hst hh hsL (hmin s (left_mem_Icc.mpr hst))
  refine ⟨he.1, he.2, ?_, ?_⟩
  · intro x hx
    exact (descendingSet_spec hst hh htL (hmin s (left_mem_Icc.mpr hst)) hx).1
  · intro x y hxy
    exact descendingSet_step hst hh htL hmin hxy.1 hxy.2.1 hxy.2.2.1 hxy.2.2.2

theorem ascendingSet_good {h : ℝ → ℝ} {L : Finset ℝ} {s t : ℝ}
    (hst : s ≤ t) (hh : ContinuousOn h (Icc s t)) (hsL : h s ∈ L) (htL : h t ∈ L)
    (hmin : ∀r ∈ Icc s t, h s ≤ h r) :
    GoodSampling (HeightStep h L) s t (ascendingSet h L s t) := by
  have he := ascendingSet_endpoints hst hh htL (hmin t (right_mem_Icc.mpr hst))
  refine ⟨he.1, he.2, ?_, ?_⟩
  · intro x hx
    exact (ascendingSet_spec hst hh hsL (hmin t (right_mem_Icc.mpr hst)) hx).1
  · intro x y hxy
    exact ascendingSet_step hst hh hsL hmin hxy.1 hxy.2.1 hxy.2.2.1 hxy.2.2.2

/-- A genuinely constructed finite sampling of one interval, using first
crossings down to a minimum and last crossings up from it. -/
theorem exists_goodSampling_of_minimum {h : ℝ → ℝ} {L : Finset ℝ} {s t r : ℝ}
    (hh : ContinuousOn h (Icc s t)) (hr : r ∈ Icc s t)
    (hsL : h s ∈ L) (htL : h t ∈ L) (hrL : h r ∈ L)
    (hmin : ∀q ∈ Icc s t, h r ≤ h q) :
    ∃S, GoodSampling (HeightStep h L) s t S := by
  refine ⟨descendingSet h L s r ∪ ascendingSet h L r t, goodSampling_union (b := r) ?_ ?_⟩
  · exact descendingSet_good hr.1 (hh.mono (Icc_subset_Icc le_rfl hr.2)) hsL hrL
      (fun q hq => hmin q ⟨hq.1, le_trans hq.2 hr.2⟩)
  · exact ascendingSet_good hr.2 (hh.mono (Icc_subset_Icc hr.1 le_rfl)) hrL htL
      (fun q hq => hmin q ⟨le_trans hr.1 hq.1, hq.2⟩)

def LevelEdge {E : Type*} [MetricSpace E] (o : E) (L : Finset ℝ) (x y : E) : Prop :=
  dist o x ∈ L ∧ dist o y ∈ L ∧ dist o x < dist o y ∧
  dist x y = dist o y - dist o x ∧
  ∀c ∈ L, ¬(dist o x < c ∧ c < dist o y)

/-- Edges join consecutive selected height levels along one rooted metric
segment.  Points outside the selected levels are simply isolated. -/
def levelGraph {E : Type*} [MetricSpace E] (o : E) (L : Finset ℝ) : SimpleGraph E where
  Adj x y := LevelEdge o L x y ∨ LevelEdge o L y x
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨by intro x; rintro (h | h) <;> exact lt_irrefl _ h.2.2.1⟩

theorem levelGraph_height_ne {E : Type*} [MetricSpace E] (o : E) (L : Finset ℝ)
    {x y : E} (he : (levelGraph o L).Adj x y) : dist o x ≠ dist o y := by
  rcases he with he | he
  · exact ne_of_lt he.2.2.1
  · exact (ne_of_lt he.2.2.1).symm

theorem levelGraph_lower_edge {E : Type*} [MetricSpace E] (o : E) (L : Finset ℝ)
    {x y : E} (he : (levelGraph o L).Adj x y) (hlt : dist o y < dist o x) :
    LevelEdge o L y x := by
  rcases he with he | he
  · exact False.elim (lt_asymm hlt he.2.2.1)
  · exact he

theorem equal_ancestor_of_equal_height {E : Type*} [MetricSpace E]
    (h4 : @FourPoint E _) (o x y z : E) (hxy : dist o x = dist o y)
    (hxz : dist x z = dist o z - dist o x)
    (hyz : dist y z = dist o z - dist o y) : x = y := by
  have he := h4 o x z y
  rw [dist_comm z y, hxz, hyz, ← hxy] at he
  have heq : dist o x + (dist o z - dist o x) = dist o z := by ring
  rw [heq, max_self] at he
  exact dist_eq_zero.mp (le_antisymm (by linarith) dist_nonneg)

theorem levelGraph_unique_lower {E : Type*} [MetricSpace E]
    (h4 : @FourPoint E _) (o : E) (L : Finset ℝ) {v x y : E}
    (hx : (levelGraph o L).Adj v x) (hy : (levelGraph o L).Adj v y)
    (hxl : dist o x < dist o v) (hyl : dist o y < dist o v) : x = y := by
  have ex := levelGraph_lower_edge o L hx hxl
  have ey := levelGraph_lower_edge o L hy hyl
  have heq : dist o x = dist o y := by
    rcases lt_trichotomy (dist o x) (dist o y) with hlt | heq | hlt
    · exact False.elim (ex.2.2.2.2 _ ey.1 ⟨hlt, hyl⟩)
    · exact heq
    · exact False.elim (ey.2.2.2.2 _ ex.1 ⟨hlt, hxl⟩)
  exact equal_ancestor_of_equal_height h4 o x y v heq ex.2.2.2.1 ey.2.2.2.1

/-- Every finite selection of height levels in a four-point metric space
has an acyclic rooted-segment graph.  The metric space itself need not be
finite and no unique-arc conclusion is assumed. -/
theorem levelGraph_acyclic {E : Type*} [MetricSpace E]
    (h4 : @FourPoint E _) (o : E) (L : Finset ℝ) : (levelGraph o L).IsAcyclic :=
  acyclic_of_unique_lower_neighbor (dist o)
    (fun _ _ he => levelGraph_height_ne o L he)
    (fun _ _ _ hx hy hxl hyl => levelGraph_unique_lower h4 o L hx hy hxl hyl)

theorem levelGraph_signature_cancel {ι E : Type*} [MetricSpace E]
    (h4 : @FourPoint E _) (o : E) (L : Finset ℝ) (f : E → ι → ℝ)
    {r : E} (p : (levelGraph o L).Walk r r) :
    walkWeight (fun u v => segmentSignature (f u) (f v)) p =
      (1 : LinearInputCurveWordFriedrichs.TensorSeries ι) :=
  acyclic_closed_walk_weight (levelGraph_acyclic h4 o L) _
    (fun u v _ => segmentSignature_cancel (f v) (f u)) p

theorem quotientTime_dist {h : ℝ → ℝ} {a b : ℝ}
    (hh : ContinuousOn h (Icc a b)) (s t : Icc a b) :
    dist (quotientTime hh s) (quotientTime hh t) = heightDist h s t := rfl

theorem quotientTime_root_dist {h : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hh : ContinuousOn h (Icc a b)) (ha : h a = 0)
    (hnonneg : ∀t ∈ Icc a b, 0 ≤ h t) (t : Icc a b) :
    dist (quotientTime hh ⟨a, left_mem_Icc.mpr hab⟩) (quotientTime hh t) = h t := by
  obtain ⟨r, hr, he, hmin⟩ := intervalMinimum_attained hh
    (left_mem_Icc.mpr hab) t.property
  have hr' : r ∈ Icc a b := uIcc_subset_interval (left_mem_Icc.mpr hab) t.property hr
  have hn := hnonneg r hr'
  have hl := hmin a left_mem_uIcc
  have hz : intervalMinimum h a t = 0 := by rw [he]; rw [ha] at hl; linarith
  rw [quotientTime_dist, heightDist, ha, hz]
  ring

theorem heightStep_minimum {h : ℝ → ℝ} {L : Finset ℝ} {a b x y : ℝ}
    (hh : ContinuousOn h (Icc a b)) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (hxy : x ≤ y) (he : HeightStep h L x y) :
    intervalMinimum h x y = min (h x) (h y) := by
  obtain ⟨r, hr, hm, _⟩ := intervalMinimum_attained hh hx hy
  apply le_antisymm
  · exact le_min (intervalMinimum_le hh hx hy left_mem_uIcc)
      (intervalMinimum_le hh hx hy right_mem_uIcc)
  · rw [hm]
    exact he.2.2.1 r (by simpa only [uIcc_of_le hxy] using hr)

/-- The selected height-step law produces an actual edge, or a stationary
step, in the separated metric quotient constructed from the height. -/
theorem heightStep_quotient_edge {h : ℝ → ℝ} {L : Finset ℝ} {a b : ℝ}
    (hab : a ≤ b) (hh : ContinuousOn h (Icc a b)) (ha : h a = 0)
    (hnonneg : ∀t ∈ Icc a b, 0 ≤ h t) (x y : Icc a b) (hxy : x.val ≤ y.val)
    (he : HeightStep h L x y) :
    quotientTime hh x = quotientTime hh y ∨
      (levelGraph (quotientTime hh ⟨a, left_mem_Icc.mpr hab⟩) L).Adj
        (quotientTime hh x) (quotientTime hh y) := by
  have hm := heightStep_minimum hh x.property y.property hxy he
  have hd : dist (quotientTime hh x) (quotientTime hh y) =
      h x + h y - 2 * min (h x) (h y) := by
    rw [quotientTime_dist, heightDist, hm]
  have rx := quotientTime_root_dist hab hh ha hnonneg x
  have ry := quotientTime_root_dist hab hh ha hnonneg y
  rcases lt_trichotomy (h x) (h y) with hlt | heq | hlt
  · right; left
    refine ⟨by simpa only [rx] using he.1, by simpa only [ry] using he.2.1,
      by simpa only [rx, ry] using hlt, ?_, ?_⟩
    · rw [rx, ry, hd, min_eq_left hlt.le]; ring
    · simpa only [rx, ry, min_eq_left hlt.le, max_eq_right hlt.le] using he.2.2.2
  · left
    apply dist_eq_zero.mp
    rw [hd, heq, min_self]; ring
  · right; right
    refine ⟨by simpa only [ry] using he.2.1, by simpa only [rx] using he.1,
      by simpa only [rx, ry] using hlt, ?_, ?_⟩
    · rw [dist_comm, hd, rx, ry, min_eq_right hlt.le]; ring
    · simpa only [rx, ry, min_eq_right hlt.le, max_eq_left hlt.le] using he.2.2.2

/-- A finite time grid is refined by actual first/last level hits, with one
common finite set of levels across all cells.  Inserting these hits never
increases the time mesh. -/
theorem exists_goodSampling_grid {h : ℝ → ℝ} (t : ℕ → ℝ) (N : ℕ)
    (ht : Monotone t) (hh : ContinuousOn h (Icc (t 0) (t N))) {δ : ℝ}
    (hwidth : ∀i < N, t (i + 1) - t i ≤ δ) :
    ∃(L : Finset ℝ) (S : Finset ℝ),
      GoodSampling (fun x y => HeightStep h L x y ∧ y - x ≤ δ) (t 0) (t N) S := by
  classical
  have hex : ∀i : Fin N, ∃r ∈ Icc (t i) (t (i.val + 1)),
      ∀q ∈ Icc (t i) (t (i.val + 1)), h r ≤ h q := by
    intro i
    exact isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (ht (Nat.le_succ i.val)))
      (hh.mono (Icc_subset_Icc (ht (Nat.zero_le i.val)) (ht (by omega))))
  choose r hr hmin using hex
  let L : Finset ℝ := ((Finset.range (N + 1)).image (fun i => h (t i))) ∪
    (Finset.univ.image (fun i : Fin N => h (r i)))
  have htL (i : ℕ) (hi : i ≤ N) : h (t i) ∈ L := by
    exact Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨i, Finset.mem_range.mpr (by omega), rfl⟩)
  have hrL (i : Fin N) : h (r i) ∈ L := by
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hloc : ∀i : Fin N, ∃S : Finset ℝ,
      GoodSampling (fun x y => HeightStep h L x y ∧ y - x ≤ δ)
        (t i) (t (i.val + 1)) S := by
    intro i
    obtain ⟨S, hS⟩ := exists_goodSampling_of_minimum
      (hh.mono (Icc_subset_Icc (ht (Nat.zero_le i.val)) (ht (by omega))))
      (hr i) (htL i i.isLt.le) (htL (i.val + 1) (by omega)) (hrL i) (hmin i)
    exact ⟨S, goodSampling_with_mesh hS (hwidth i i.isLt)⟩
  choose S hS using hloc
  let U : ℕ → Finset ℝ := fun i => if hi : i < N then S ⟨i, hi⟩ else ∅
  refine ⟨L, chainSamples t U N, goodSampling_chain t U N ?_⟩
  intro i hi
  simpa only [U, dite_eq_left hi] using hS ⟨i, hi⟩

/-- Arbitrarily fine chronological samples with the finite-level edge law.
This is an existence theorem for every continuous height on the interval. -/
theorem exists_height_sampling {h : ℝ → ℝ} {a b δ : ℝ} (hab : a ≤ b)
    (hh : ContinuousOn h (Icc a b)) (hδ : 0 < δ) :
    ∃(L : Finset ℝ) (N : ℕ) (t : Fin (N + 1) → ℝ),
      StrictMono t ∧ t 0 = a ∧ t (Fin.last N) = b ∧
      ∀i : Fin N, HeightStep h L (t i.castSucc) (t i.succ) ∧
        t i.succ - t i.castSucc ≤ δ := by
  obtain ⟨K, hK⟩ := exists_nat_gt ((b - a) / δ)
  have hKpos : 0 < (K : ℝ) := lt_of_le_of_lt (div_nonneg (sub_nonneg.mpr hab) hδ.le) hK
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKpos
  let grid : ℕ → ℝ := fun i => a + (b - a) * (i : ℝ) / K
  have hg0 : grid 0 = a := by simp [grid]
  have hgK : grid K = b := by simp [grid, hKne]
  have hg : Monotone grid := by
    intro i j hij
    dsimp [grid]
    exact add_le_add le_rfl (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (show (i : ℝ) ≤ (j : ℝ) by exact_mod_cast hij)
        (sub_nonneg.mpr hab)) hKpos.le)
  have hw : ∀i < K, grid (i + 1) - grid i ≤ δ := by
    intro i _
    have hd : (b - a) / (K : ℝ) < δ := (div_lt_iff₀ hKpos).mpr
      (by have he := (div_lt_iff₀ hδ).mp hK; nlinarith)
    calc
      grid (i + 1) - grid i = (b - a) / (K : ℝ) := by dsimp [grid]; push_cast; ring
      _ ≤ δ := hd.le
  obtain ⟨L, S, hS⟩ := exists_goodSampling_grid grid K hg
    (by simpa only [hg0, hgK] using hh) hw
  obtain ⟨N, t, ht, ht0, htN, _, he⟩ := goodSampling_enumeration hS
  exact ⟨L, N, t, ht, ht0.trans hg0, htN.trans hgK, he⟩

end LinearInputCurveWordTreeSampling
