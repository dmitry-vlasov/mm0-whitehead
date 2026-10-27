/-
The declarations of the theory, for `docs/CORRESPONDENCE.md`: every constant of the
`Theory.*` modules with its kind, file and line, docstring, pretty-printed statement,
and the constants of the theory its statement and its proof use (auxiliary constants
of mutual and well-founded recursion — `match_n`, `_unary`, `eq_n`, `below`, … —
expanded into what they use). Run from `theory/`:

    mkdir -p tools/out && lake env lean tools/Extract.lean

Writes `tools/out/decls.jsonl` and `tools/out/modules.jsonl` (one JSON object per
declaration, pretty-printed over several lines; `correspondence.py` reads them).
-/
import Theory
import Lean
open Lean Meta

namespace Extract

def allDigits (l : List Char) : Bool := l.length > 0 && l.all Char.isDigit

def auxLast (s : String) : Bool :=
  s.startsWith "_" ||
  (s.startsWith "match_" && allDigits (s.toList.drop 6)) ||
  (s.startsWith "proof_" && allDigits (s.toList.drop 6)) ||
  (s.startsWith "eq_" && allDigits (s.toList.drop 3)) ||
  s ∈ ["rec", "recOn", "casesOn", "below", "brecOn", "binductionOn", "ibelow", "induct",
       "mutual_induct", "noConfusion", "noConfusionType", "sizeOf_spec", "injEq", "inj",
       "ctorIdx", "toCtorIdx", "ctorElim", "ctorElimType", "eq_def", "eq_unfold", "sizeOf",
       "fun_cases", "fun_cases_unfolding", "induct_unfolding", "mutual_induct_unfolding", "mk", "ofNat", "toNat"]

partial def isAux : Name → Bool
  | .str p s => auxLast s || isAux p
  | .num _ _ => true
  | .anonymous => false

def kindOf (env : Environment) (n : Name) (ci : ConstantInfo) : MetaM String := do
  match ci with
  | .thmInfo _ => return "theorem"
  | .inductInfo _ => if isStructure env n then return (if isClass env n then "class" else "structure") else return "inductive"
  | .ctorInfo _ => return "constructor"
  | .defnInfo _ =>
    if ← isInstance n then return "instance"
    match ← getReducibilityStatus n with
    | .reducible => return "abbrev"
    | _ => return "def"
  | .opaqueInfo _ => return "opaque"
  | .axiomInfo _ => return "axiom"
  | .recInfo _ => return "recursor"
  | .quotInfo _ => return "quot"

/-- Direct uses, with auxiliary constants of our modules expanded transitively. -/
partial def deps (env : Environment) (isOurs : Name → Bool) (e : Expr) (acc : NameSet) (visited : NameSet) :
    NameSet × NameSet := Id.run do
  let mut acc := acc
  let mut visited := visited
  for c in e.getUsedConstants do
    if !isOurs c then continue
    if isAux c then
      if visited.contains c then continue
      visited := visited.insert c
      match env.find? c with
      | some ci =>
        let (a, v) := deps env isOurs ci.type acc visited
        acc := a; visited := v
        match ci.value? (allowOpaque := true) with
        | some val =>
          let (a, v) := deps env isOurs val acc visited
          acc := a; visited := v
        | none => pure ()
      | none => pure ()
    else
      acc := acc.insert c
  return (acc, visited)

def run (out : String) : MetaM Unit := do
  let env ← getEnv
  let mods := env.header.moduleNames
  let isTheoryMod (m : Name) : Bool := (`Theory).isPrefixOf m && m != `Theory
  let isOurs (c : Name) : Bool :=
    match env.getModuleIdxFor? c with
    | some idx => isTheoryMod mods[idx.toNat]!
    | none => false
  let mut lines : Array String := #[]
  -- module import graph
  let mut modLines : Array String := #[]
  for h : idx in [0:mods.size] do
    let m := mods[idx]
    if isTheoryMod m then
      let imps := env.header.moduleData[idx]!.imports.map (·.module) |>.filter isTheoryMod
      modLines := modLines.push (toString (Json.mkObj [("module", toString m), ("imports", toJson (imps.map toString))]))
  for h : idx in [0:mods.size] do
    let m := mods[idx]
    if !isTheoryMod m then continue
    let data := env.header.moduleData[idx]!
    for ci in data.constants do
      let n := ci.name
      if isAux n then continue
      let kind ← kindOf env n ci
      let rng? ← findDeclarationRanges? n
      let (line, endLine) := match rng? with
        | some r => (r.range.pos.line, r.range.endPos.line)
        | none => (0, 0)
      let doc? ← findDocString? env n
      let tyFmt ← withOptions (fun o => o.setBool `pp.universes false) (ppExpr ci.type)
      let tyStr := toString (tyFmt.pretty 110)
      let (tdeps, _) := deps env isOurs ci.type {} {}
      let (vdeps, _) := match ci.value? (allowOpaque := true) with
        | some v => deps env isOurs v {} {}
        | none => ({}, {})
      let tdepsL := tdeps.toList.filter (· != n) |>.map toString
      let vdepsL := vdeps.toList.filter (· != n) |>.map toString
      let j := Json.mkObj [
        ("name", toString n), ("module", toString m), ("kind", kind),
        ("line", toJson line), ("endLine", toJson endLine),
        ("doc", match doc? with | some d => toJson d | none => Json.null),
        ("type", tyStr), ("typeDeps", toJson tdepsL), ("valueDeps", toJson vdepsL),
        ("isUnsafe", toJson ci.isUnsafe)]
      lines := lines.push (toString j)
  IO.FS.writeFile (out ++ "/decls.jsonl") (String.intercalate "\n" lines.toList ++ "\n")
  IO.FS.writeFile (out ++ "/modules.jsonl") (String.intercalate "\n" modLines.toList ++ "\n")
  IO.println s!"{lines.size} declarations, {modLines.size} modules"

end Extract

open Theory in
#eval Extract.run "tools/out"
