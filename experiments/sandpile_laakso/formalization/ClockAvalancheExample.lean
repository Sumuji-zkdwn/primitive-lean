import Std

/-! A finite, kernel-evaluated 8 × 8 wired sandpile. Each Nat contains 64
base-65536 digits in row-major order; each digit is the height at one site.
For the computations below all stable heights are at most 3. Adding one grain
or the sink edges produces heights at most 5. In each parallel round a site
retains at most 3 grains and receives at most 4. Thus all heights stay below
8, and arithmetic on neighboring digits never carries or borrows. Each site
selected for the round can legally fire once in any order.

Run with `elan run leanprover/lean4:v4.35.0 lean --trust=0 ClockAvalancheExample.lean`.
No theorem about unbounded board sizes is used or asserted. -/
namespace ClockAvalancheExample

def pack (digits : List Nat) : Nat :=
  digits.foldr (fun h rest => h + (rest <<< 16)) 0

def mask (f : Nat → Nat) : Nat := pack ((List.range 64).map f)
def units := mask fun _ => 1
def exceptLeft := mask fun k => if k % 8 == 0 then 0 else 1
def exceptRight := mask fun k => if k % 8 == 7 then 0 else 1

/-- Coefficient at digit 63 of the product with the reversed weights.
The largest sum contributing to any digit for these weights is bounded
by 64 × 7 × 64 < 65536, so the coefficient equals the ordinary dot product. -/
def weightedSum (board reversedWeights : Nat) : Nat :=
  ((board * reversedWeights) >>> 1008) % 65536

def reversedMask (f : Nat → Nat) := mask (fun k => f (63-k))
def clockWeights := reversedMask fun k => (k / 8 + 1) * (k % 8 + 1)

/-- The explicit Dirichlet fields from SquareClock, grouped by the two
periods at M=9. Columns divisible by 3 have period 3; the others have period 9. -/
def field (i j q : Nat) : Nat :=
  if i+j > q ∧ i+q > j ∧ j+q > i ∧ i+j+q < 18 ∧ (i+j+q)%2 = 1 then 1 else 0
def bitWeights (short : Bool) := reversedMask fun k =>
  (((List.range 8).map fun c =>
      if ((c+1)%3 == 0) == short then field (k/8+1) (k%8+1) (c+1) else 0).sum) % 2
def observation (board : Nat) : Nat × Nat × Nat :=
  ((5 * weightedSum board clockWeights) % 9,
   weightedSum board (bitWeights true) % 2, weightedSum board (bitWeights false) % 2)

def receive (active : Nat) : Nat :=
  (active >>> 128) + ((active <<< 128) &&& units)
   + ((active &&& exceptLeft) >>> 16) + ((active &&& exceptRight) <<< 16)

structure Avalanche where
  board : Nat
  count : Nat
  fired : Nat
  deriving DecidableEq

/-- Return none if the round budget expires on an unstable board. The fired
mask records all sites that fired at least once, and count counts repetitions. -/
def stabilize : Nat → Avalanche → Option Avalanche
  | fuel, s =>
    let active := (s.board >>> 2) &&& units
    if active == 0 then some s else
      match fuel with
      | 0 => none
      | n+1 => stabilize n
          ⟨s.board - (active <<< 2) + receive active,
           s.count + weightedSum active units, s.fired ||| active⟩

def initialRows : List (List Nat) :=
  [[3,1,3,1,1,3,2,1], [1,3,1,0,2,1,3,2],
   [3,1,1,3,3,1,1,3], [1,2,3,3,3,3,2,1],
   [3,3,3,3,3,3,3,3], [3,3,3,3,3,3,3,3],
   [3,3,3,3,3,3,3,3], [3,3,3,3,3,3,3,3]]
def first := pack initialRows.flatten
def second := pack ((initialRows.map List.reverse).flatten)

/-- Dhar's burning test, adding one grain per missing neighbor. Returning to
the same board with 64 firings on 64 distinct sites gives a burning certificate. -/
def burn (b : Nat) : Bool :=
  let boundary := mask fun k =>
    (if k/8 == 0 then 1 else 0) + (if k/8 == 7 then 1 else 0)
     + (if k%8 == 0 then 1 else 0) + (if k%8 == 7 then 1 else 0)
  stabilize 64 ⟨b+boundary, 0, 0⟩ == some ⟨b, 64, units⟩

structure PairState where
  a : Avalanche
  b : Avalanche

/-- Apply the same grain to each board and reject if the angles or bits differ
after stabilization. This tests both half-steps of every two-grain input. -/
def nextGrain (s : PairState) (site : Nat) : Option PairState := do
  let a ← stabilize 64 { s.a with board := s.a.board + (1 <<< (16 * site)) }
  let b ← stabilize 64 { s.b with board := s.b.board + (1 <<< (16 * site)) }
  guard (observation a.board == observation b.board)
  return ⟨a,b⟩

def twoGrains (s : PairState) (site : Nat) : Option PairState := do
  let half ← nextGrain s site
  nextGrain half site

/-- Forty alternating left/right pairs followed by one left input = 81
two-grain inputs. Return the two counts both before and after the last input. -/
def replay : Option (Nat × Nat × Nat × Nat) := do
  guard (weightedSum first units == 158 && weightedSum second units == 158)
  guard (burn first && burn second && observation first == observation second)
  let start : PairState := ⟨⟨first, 0, 0⟩, ⟨second, 0, 0⟩⟩
  let pre ← (List.range 80).foldlM (fun s j => twoGrains s (if j%2 == 0 then 0 else 7)) start
  let post ← twoGrains pre 0
  return (pre.a.count, pre.b.count, post.a.count, post.b.count)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem balanced_example : replay = some (95, 95, 95, 158) := by decide +kernel

#print axioms balanced_example
end ClockAvalancheExample
