/-! Runtime transition export for independent comparison with the pinned
Python Economy. This is test data, not an extra proof axiom. -/
namespace Elastica.ChairInternalGeneration.Export

def encode (s : State) : Nat :=
  s.capability.val * 8 + s.chair.toNat * 4 + s.demand.toNat * 2 + s.paid.toNat

def oldActions : List (Internal ⊕ Gate) :=
  [.inl .grow, .inl .sale, .inr .chair, .inr .demand]

def newActions : List ((Internal ⊕ Unit) ⊕ Gate) :=
  [.inl (.inl .grow), .inl (.inl .sale), .inr .chair, .inr .demand, .inl (.inr ())]

def printTransitions : IO Unit := do
  for c in List.finRange 4 do
    for ch in [false, true] do
      for d in [false, true] do
        for p in [false, true] do
          let s : State := ⟨c, ch, d, p⟩
          for (a, idx) in oldActions.zipIdx do
            IO.println s!"TRANS old {encode s} {idx} {encode (oldStep a s)}"
          for (a, idx) in newActions.zipIdx do
            IO.println s!"TRANS new {encode s} {idx} {encode (newStep a s)}"

#eval printTransitions

end Elastica.ChairInternalGeneration.Export
