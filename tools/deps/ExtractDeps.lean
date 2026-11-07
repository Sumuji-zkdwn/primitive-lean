/-
Dependency extractor for kernel-accepted declarations.

Usage (from `lean/`, with the compiled modules on LEAN_PATH):
  lake env lean --run ../tools/deps/ExtractDeps.lean OUT.json Mod1 Mod2 ... -- Prefix1 Prefix2 ...

For every constant whose module name starts with one of the project prefixes
it records, separately,
  * `type_consts`  : constants occurring in the declared type (statement),
  * `value_consts` : constants occurring in the value. For a theorem this is
                     the elaborated proof term; for a definition it is the body.
  * `head`         : the head constant of the value after stripping binders
                     and metadata (used only as a heuristic signal).
It also records the module of every referenced non-project constant and the
import lists of the project modules. Nothing here judges mathematical
necessity: an occurrence in a term is an occurrence, nothing more.
-/
import Lean
open Lean

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "recursor"

partial def stripBinders : Expr → Expr
  | .lam _ _ b _ => stripBinders b
  | .mdata _ b => stripBinders b
  | e => e

def namesJson (xs : Array Name) : Json :=
  Json.arr (xs.qsort (fun a b => a.toString < b.toString) |>.map (fun n => Json.str n.toString))

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => `_current

def main (args : List String) : IO Unit := do
  let out :: rest := args | throw <| IO.userError "usage: OUT.json Mod... -- Prefix..."
  let (mods, pfx) := rest.span (· != "--")
  let prefixes := (pfx.drop 1).map String.toName |>.toArray
  initSearchPath (← findSysroot)
  let imports := mods.toArray.map fun m => ({ module := m.toName } : Import)
  let env ← importModules imports {} (trustLevel := 1024) (loadExts := false)
  let isProject (m : Name) : Bool := prefixes.any (·.isPrefixOf m)
  let mut decls : Array Json := #[]
  let mut external : Std.HashMap Name Name := {}
  let projectIdx := (List.range env.header.moduleNames.size).filter
    (fun i => isProject env.header.moduleNames[i]!)
  let names : Array Name := projectIdx.foldl
    (fun acc i => acc ++ env.header.moduleData[i]!.constNames) #[]
  let mut visited : Std.HashSet Name := {}
  for n in names do
    if visited.contains n then continue
    visited := visited.insert n
    let some ci := env.find? n | continue
    let m := moduleOf env n
    let tc := ci.type.getUsedConstants
    let vc := match ci.value? (allowOpaque := true) with
      | some v => v.getUsedConstants
      | none => #[]
    for c in tc ++ vc do
      let cm := moduleOf env c
      unless isProject cm do external := external.insert c cm
    let head := match ci.value? (allowOpaque := true) with
      | some v =>
        let b := stripBinders v
        match b.getAppFn with
        | .const h _ => Json.mkObj [("const", Json.str h.toString), ("args", Json.num b.getAppNumArgs)]
        | _ => Json.null
      | none => Json.null
    let line : Json := match declRangeExt.find? env n with
      | some r => Json.num r.range.pos.line
      | none => Json.null
    decls := decls.push <| Json.mkObj [
      ("name", Json.str n.toString), ("kind", Json.str (kindOf ci)),
      ("module", Json.str m.toString), ("line", line),
      ("internal", Json.bool n.isInternal), ("type_consts", namesJson tc),
      ("value_consts", namesJson vc), ("head", head)]
  let mut ext : Array Json := #[]
  for (c, m) in external.toList do
    let k := match env.find? c with | some ci => kindOf ci | none => "unknown"
    ext := ext.push <| Json.mkObj [("name", Json.str c.toString), ("module", Json.str m.toString), ("kind", Json.str k)]
  let mut modImports : Array Json := #[]
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if isProject m then
      let ims := env.header.moduleData[i]!.imports.map (·.module)
      modImports := modImports.push <| Json.mkObj [("module", Json.str m.toString), ("imports", namesJson ims)]
  let doc := Json.mkObj [("declarations", Json.arr decls), ("external", Json.arr ext), ("module_imports", Json.arr modImports)]
  IO.FS.writeFile out doc.compress
  IO.println s!"declarations={decls.size} external={ext.size} project_modules={modImports.size}"
