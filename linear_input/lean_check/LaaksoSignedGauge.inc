/-! Vertex switching for the signed, six-edge first Laakso approximant.
The spanning tree omits edge 3. Its five signs can be removed by a change
of vertex labels, leaving the parity of the two parallel middle edges. -/

noncomputable section

namespace LinearInputLaaksoSignedGauge

open LinearInputLaaksoFiniteGraph LinearInputLaaksoSigned LinearInputLaaksoSignedEnergy

/-- Switch every edge at both of its endpoints. -/
def switchTwist (g : Spin) (τ : Twist) : Twist := fun e =>
  xor (xor (g (firstSource e)) (τ e)) (g (firstTarget e))

theorem switch_involutive (g : Spin) (τ : Twist) :
    switchTwist g (switchTwist g τ) = τ := by
  funext e
  unfold switchTwist
  cases g (firstSource e) <;> cases τ e <;> cases g (firstTarget e) <;> rfl

theorem parity_switch (g : Spin) (τ : Twist) :
    middleParity (switchTwist g τ) = middleParity τ := by
  change xor (xor (xor (g 4) (τ 2)) (g 5)) (xor (xor (g 4) (τ 3)) (g 5)) = _
  unfold middleParity
  cases g 4 <;> cases g 5 <;> cases τ 2 <;> cases τ 3 <;> rfl

/-- Propagate vertex labels from vertex 4 over the five tree edges. -/
def treeGauge (τ : Twist) : Spin :=
  ![τ 0, τ 1, xor (τ 2) (τ 4), xor (τ 2) (τ 5), false, τ 2]

theorem tree_normal_form (τ : Twist) :
    switchTwist (treeGauge τ) τ = if middleParity τ then flipped else untwisted := by
  funext e
  cases h2 : τ 2 <;> cases h3 : τ 3 <;>
    fin_cases e <;>
    simp [switchTwist, treeGauge, firstSource, firstTarget, middleParity,
      flipped, untwisted, h2, h3]

/-- Two signatures differ by a vertex switching exactly when their cycle
parities agree. Pointwise XOR composes the two tree normalizations. -/
theorem switch_equivalent_iff (τ υ : Twist) :
    (∃ g : Spin, switchTwist g τ = υ) ↔ middleParity τ = middleParity υ := by
  constructor
  · rintro ⟨g, rfl⟩
    exact (parity_switch g τ).symm
  · intro h
    have common : switchTwist (treeGauge τ) τ = switchTwist (treeGauge υ) υ := by
      rw [tree_normal_form, tree_normal_form, h]
    refine ⟨fun v => xor (treeGauge τ v) (treeGauge υ v), ?_⟩
    calc
      _ = switchTwist (treeGauge υ) (switchTwist (treeGauge τ) τ) := by
        funext e
        simp only [switchTwist]
        cases treeGauge τ (firstSource e) <;> cases treeGauge υ (firstSource e) <;>
          cases treeGauge τ (firstTarget e) <;> cases treeGauge υ (firstTarget e) <;>
          cases τ e <;> rfl
      _ = υ := by rw [common, switch_involutive]

/-- Change both components of the local state along with its vertex label. -/
def switchState (g : Spin) (q : State) : State :=
  fun v => if g v then (-(q v).1, -(q v).2) else q v

theorem localPotential_switch (g : Spin) (q : State) (v : Fin 6) :
    localPotential (switchState g q v) = localPotential (q v) := by
  cases h : g v with
  | false => simp [switchState, h]
  | true => simp [switchState, localPotential, h]; ring

theorem edgeEnergy_switch (g : Spin) (τ : Twist) (q : State) (e : Fin 6) :
    edgeEnergy (switchTwist g τ) (switchState g q) e = edgeEnergy τ q e := by
  cases hs : g (firstSource e) <;> cases ht : g (firstTarget e) <;> cases he : τ e <;>
    simp [edgeEnergy, switchState, switchTwist, sign, hs, ht, he] <;> ring

theorem energy_switch (g : Spin) (τ : Twist) (q : State) :
    energy (switchTwist g τ) (switchState g q) = energy τ q := by
  simp only [energy, localPotential_switch, edgeEnergy_switch]

theorem odd_energy_lower_bound {τ : Twist} (h : middleParity τ = true) (q : State) :
    1 / 2 ≤ energy τ q := by
  rw [← energy_switch (treeGauge τ) τ q, tree_normal_form, h]
  exact energy_flipped_lower_bound _

/-- Balanced signatures admit a zero-energy state; every other signature
has the all-state lower bound of the flipped representative. -/
theorem zero_energy_iff (τ : Twist) :
    (∃ q : State, energy τ q = 0) ↔ middleParity τ = false := by
  constructor
  · rintro ⟨q, hq⟩
    cases hp : middleParity τ with
    | false => rfl
    | true =>
      have bound := odd_energy_lower_bound hp q
      rw [hq] at bound
      norm_num at bound
  · intro hp
    have normalized : switchTwist (treeGauge τ) τ = untwisted := by
      rw [tree_normal_form, hp]
      rfl
    have back : switchTwist (treeGauge τ) untwisted = τ := by
      rw [← normalized, switch_involutive]
    refine ⟨switchState (treeGauge τ) constantWell, ?_⟩
    have conserved := energy_switch (treeGauge τ) untwisted constantWell
    rw [back, energy_untwisted_constantWell] at conserved
    exact conserved

end LinearInputLaaksoSignedGauge

end
