/-
Detect re-defined copies of initial definitions.

Usage (from `lean/`, compiled modules on LEAN_PATH):
  lake env lean --run ../tools/deps/CopyCheck.lean OUT.json CANDIDATES.txt INITIAL.txt Mod1 Mod2 ...

For every candidate C (a definition introduced without touching the initial
layer) and every initial definition I (universe parameters instantiated by fresh level
metavariables), it
asks the elaborator's definitional-equality check, under default transparency
and a heartbeat budget:
  1. are the declared types definitionally equal?
  2. if so, are the constants themselves definitionally equal (`C =?= I`)?
`true` in (2) means C is a copy of I up to unfolding. `false` or a timeout means
only that this check did not identify them; it does not prove they differ.
-/
import Lean
open Lean Meta

def readLines (p : System.FilePath) : IO (Array String) := do
  let s ← IO.FS.readFile p
  return ((s.splitOn "\n").filter (· ≠ "")).toArray

/-- Resolve printed names against the constants of non-library modules, so that
private names with numeric components round-trip exactly. -/
def resolve (env : Environment) (xs : Array String) : Array Name × Array String := Id.run do
  let lib := [`Mathlib, `Init, `Lean, `Std, `Batteries, `Aesop, `Qq, `Plausible, `ProofWidgets, `ImportGraph, `LeanSearchClient]
  let mut m : Std.HashMap String Name := {}
  for i in [0:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[i]!
    if lib.any (·.isPrefixOf mod) then continue
    for n in env.header.moduleData[i]!.constNames do
      m := m.insert n.toString n
  let mut ok := #[]
  let mut missing := #[]
  for x in xs do
    match m.get? x with
    | some n => ok := ok.push n
    | none => missing := missing.push x
  return (ok, missing)

/-- `none`: missing constant or an exception while comparing types; `some (false, none)`: types differ;
`some (true, v)`: types agree and `v` is the verdict on the constants (`none` = timeout/error). -/
def pair (a b : Name) : MetaM (Option (Bool × Option Bool)) := do
  let env ← getEnv
  unless env.contains a && env.contains b do return none
  try
    withoutModifyingState do
      -- Universe parameters become fresh level metavariables, so polymorphic
      -- definitions are compared by unification rather than skipped.
      let ea ← mkConstWithFreshMVarLevels a
      let eb ← mkConstWithFreshMVarLevels b
      if !(← isDefEq (← inferType ea) (← inferType eb)) then return some (false, none)
      let v ← try some <$> isDefEq ea eb catch _ => pure none
      return some (true, v)
  catch _ => return none

def main (args : List String) : IO Unit := do
  let out :: cand :: init :: mods := args | throw <| IO.userError "usage"
  initSearchPath (← findSysroot)
  let env ← importModules (mods.toArray.map fun m => ({ module := m.toName } : Import)) {} (trustLevel := 1024)
  let (cs, missC) := resolve env (← readLines cand)
  let (is, missI) := resolve env (← readLines init)
  let ctx : Core.Context := { fileName := "<copycheck>", fileMap := default, maxHeartbeats := 20000 * 1000 }
  let mut rows : Array Json := #[]
  let mut typeMatches := 0
  let mut copies := 0
  let mut skipped := 0
  for c in cs do
    for i in is do
      let (r, _) ← ((pair c i).run' {}).toIO ctx { env := env }
      match r with
      | none => skipped := skipped + 1
      | some (false, _) => pure ()
      | some (true, v) =>
        typeMatches := typeMatches + 1
        if v == some true then copies := copies + 1
        let verdict := match v with
          | some true => "definitionally_equal" | some false => "not_identified" | none => "timeout_or_error"
        rows := rows.push <| Json.mkObj [("candidate", Json.str c.toString), ("initial", Json.str i.toString),
          ("value", Json.str verdict)]
  let doc := Json.mkObj [("candidates", Json.num cs.size), ("initial_definitions", Json.num is.size),
    ("unresolved_names", Json.arr ((missC ++ missI).map Json.str)),
    ("pairs_skipped", Json.num skipped), ("type_matches", Json.num typeMatches),
    ("copies", Json.num copies), ("rows", Json.arr rows)]
  IO.FS.writeFile out doc.pretty
  IO.println s!"candidates={cs.size} initial={is.size} unresolved={missC.size + missI.size} type_matches={typeMatches} copies={copies} skipped={skipped}"
