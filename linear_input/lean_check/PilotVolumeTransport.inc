/-!
# Transport distortion and local packet budget for pilot comparison

This supplements PilotComparisonBridge.inc without changing it.

The key separation is between:
* shifts in log-volume induced by admissible transports; and
* an arithmetic lower bound on the actual log-shell container.

Volume-neutral Kummer transports cannot create the missing degree budget.
A packetwise budget suffices, but its existence is an arithmetic hypothesis,
not a theorem of this file. These are abstract results, not an IUT proof.
-/

noncomputable section

namespace LinearInputPilotTransport

/-- If a transport changes log-volume by an exactly known shift, the
choice-dependent comparison has an exact numerical solvability criterion.
Surjectivity of the downwards volume window is an explicit hypothesis. -/
theorem shifted_wall_iff {S G : Type*}
    (a scale cap : ℝ)
    (volume : S → ℝ) (transport : G → S → S) (shift : G → ℝ)
    (hchange : ∀ g s, volume (transport g s) = volume s + shift g)
    (hupper : ∀ s, volume s ≤ cap)
    (hcomplete : ∀ v, v ≤ cap → ∃ s, volume s = v) :
    (∃ g s, -(scale * a) + volume (transport g s) = -a) ↔
      ∃ g, (scale - 1) * a - shift g ≤ cap := by
  constructor
  · rintro ⟨g, s, hs⟩
    have hu := hupper s
    rw [hchange g s] at hs
    refine ⟨g, ?_⟩
    nlinarith
  · rintro ⟨g, hg⟩
    obtain ⟨s, hs⟩ := hcomplete _ hg
    refine ⟨g, s, ?_⟩
    rw [hchange g s, hs]
    ring

/-- Once every allowed transport is volume-neutral, changing the
transport choice cannot create new log-volume values. -/
theorem neutral_transport_wall_iff {S G : Type*}
    (a scale cap : ℝ)
    (volume : S → ℝ) (transport : G → S → S) (shift : G → ℝ)
    (hG : Nonempty G)
    (hchange : ∀ g s, volume (transport g s) = volume s + shift g)
    (hneutral : ∀ g, shift g = 0)
    (hupper : ∀ s, volume s ≤ cap)
    (hcomplete : ∀ v, v ≤ cap → ∃ s, volume s = v) :
    (∃ g s, -(scale * a) + volume (transport g s) = -a) ↔
      (scale - 1) * a ≤ cap := by
  rw [shifted_wall_iff a scale cap volume transport shift hchange hupper hcomplete]
  constructor
  · rintro ⟨g, hg⟩
    simpa only [hneutral g, sub_zero] using hg
  · intro hb
    obtain ⟨g⟩ := hG
    refine ⟨g, ?_⟩
    simpa only [hneutral g, sub_zero] using hb

/-- A uniform upper bound on permitted volume shifts imposes a
correspondingly shifted arithmetic lower bound on the container. -/
theorem bounded_shift_forces_budget {S G : Type*}
    (a scale cap allowance : ℝ)
    (volume : S → ℝ) (transport : G → S → S) (shift : G → ℝ)
    (hchange : ∀ g s, volume (transport g s) = volume s + shift g)
    (hupper : ∀ s, volume s ≤ cap)
    (hshift : ∀ g, shift g ≤ allowance)
    (h : ∃ g s, -(scale * a) + volume (transport g s) = -a) :
    (scale - 1) * a ≤ cap + allowance := by
  obtain ⟨g, s, hs⟩ := h
  have hu := hupper s
  have hg := hshift g
  rw [hchange g s] at hs
  nlinarith

/-- Explicit no-go criterion even with arbitrary many transport choices. -/
theorem bounded_shift_cannot_bridge_gap {S G : Type*}
    (a scale cap allowance : ℝ)
    (volume : S → ℝ) (transport : G → S → S) (shift : G → ℝ)
    (hchange : ∀ g s, volume (transport g s) = volume s + shift g)
    (hupper : ∀ s, volume s ≤ cap)
    (hshift : ∀ g, shift g ≤ allowance)
    (hgap : cap + allowance < (scale - 1) * a) :
    ¬ (∃ g s, -(scale * a) + volume (transport g s) = -a) := by
  intro h
  exact (not_le_of_gt hgap)
    (bounded_shift_forces_budget a scale cap allowance volume transport shift
      hchange hupper hshift h)

/-- The exact packet-sum form of a comparison wall. This mirrors the
shape of the finite capsule average in LANA's ssIneq_iff_packets; it
does not identify these abstract packets with actual arithmetic ones. -/
theorem packet_wall_iff_total_bound {I : Type*} [Fintype I] [Nonempty I]
    (packet : I → ℝ) (a scale : ℝ) :
    (scale - 1) * a ≤ (∑ i, packet i) / (Fintype.card I : ℝ) ↔
      (Fintype.card I : ℝ) * ((scale - 1) * a) ≤ ∑ i, packet i := by
  have hc : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card I)
  constructor
  · intro h
    have ht := (le_div_iff₀ hc).mp h
    simpa only [mul_comm] using ht
  · intro h
    apply (le_div_iff₀ hc).2
    simpa only [mul_comm] using h

/-- Distribute the global numerical burden among finitely many packets.
The existence of such a feasible allocation is *not* asserted. -/
theorem packet_budget_suffices {I : Type*} [Fintype I]
    (packet charge : I → ℝ) (a scale : ℝ)
    (hcharge : (∑ i, charge i) =
      (Fintype.card I : ℝ) * ((scale - 1) * a))
    (hlower : ∀ i, charge i ≤ packet i) :
    (Fintype.card I : ℝ) * ((scale - 1) * a) ≤ ∑ i, packet i := by
  rw [← hcharge]
  exact Finset.sum_le_sum (fun i _ => hlower i)

/-- When a charge allocation is established for genuine local packet
volumes, the averaged wall bound follows. The allocation is required. -/
theorem packet_budget_yields_wall {I : Type*} [Fintype I] [Nonempty I]
    (packet charge : I → ℝ) (a scale : ℝ)
    (hcharge : (∑ i, charge i) =
      (Fintype.card I : ℝ) * ((scale - 1) * a))
    (hlower : ∀ i, charge i ≤ packet i) :
    (scale - 1) * a ≤ (∑ i, packet i) / (Fintype.card I : ℝ) := by
  exact (packet_wall_iff_total_bound packet a scale).2
    (packet_budget_suffices packet charge a scale hcharge hlower)

end LinearInputPilotTransport
