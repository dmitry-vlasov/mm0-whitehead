/-
The data of the learned ranking layer (`docs/DESIGN.md`, "The learned ranking layer"): for
a theorem, the full expansion along its known proof (`oracleAll`, as `nodeCounts` makes
it), and at each goal node of the path its variants, each a row of features
(`Env.features`), the known proof's labelled 1.

This is the dataset of the author's Russell (`ml/learning_data.flow`,
`ml/collect_data.flow`): the contexts of an assertion, positive where the known proof
uses it and negative where it does not.

The rows of a node are all its variants, or the known one and `negatives` others drawn
from them; the draw is fixed by the node, so the same export gives the same rows.
-/
import Whitehead.Prove.Features
import Whitehead.Prove.Measure

namespace Whitehead.Prove

/-- The header of the rows: the theorem by number and name, the goal node, the label, the
assertion (or -1 for a conversion), the number of the node's variants, and the features. -/
def datasetHeader : String :=
  "\t".intercalate (["thm", "name", "node", "label", "assertion", "variants"] ++ featureNames.toList)

/-- A number for a draw, from two: a step of xorshift. -/
def mixHash (a b : Nat) : Nat := Id.run do
  let mut x : UInt64 := (a.toUInt64 * 0x9E3779B97F4A7C15) ^^^ (b.toUInt64 + 0x632BE59BD9B4E019)
  x := x ^^^ (x <<< 13)
  x := x ^^^ (x >>> 7)
  x := x ^^^ (x <<< 17)
  return x.toNat

/-- A proof of the search as a skeleton, the assertions it applies: none if it unfolds a
definition by a step of its own (`ProofTree.conv`), which a skeleton has no place for. -/
partial def ProofTree.skeleton? : ProofTree → Option Skeleton
  | .hyp i => some (.hyp i)
  | .step a _ cs => do return .step a (← cs.mapM ProofTree.skeleton?)
  | .conv .. => none

/-- The rows of statement `i` of the file, a theorem, along the proof `skel`. -/
def datasetRowsOf (db : Db) (index : Index Nat) (limits : Limits) (uses : Uses) (stats : SymbolStats)
    (negatives : Nat) (i : Nat) (skel : Skeleton) : IO (Array String) := do
    let s := db.file.stmts[i]!
    let env := { Env.init db index (db.task s.index) with uses }
    let r ← searchWith acceptAny env (oracleAll skel (some 0)) limits
    let env := r.env
    let mut seen : Std.HashSet Nat := {}
    let mut out := #[]
    for p in [0:env.props.size] do
      let prop := env.props[p]!
      if !prop.expanded || seen.contains prop.parent then continue
      seen := seen.insert prop.parent
      let kids := env.hyps[prop.parent]!.children
      let others := kids.filter (· != p)
      let chosen := if negatives == 0 || others.size ≤ negatives then others
        else (others.qsort fun a b => mixHash prop.parent a < mixHash prop.parent b).extract 0 negatives
      -- in the order the variants were made, the engine's own, which breaks its ties
      for q in kids.filter fun q => q == p || chosen.contains q do
        let a : Int := match env.props[q]!.step with
          | .assertion id => if (db.asserts[id]?.bind (·.pseudo)).isNone then id else -1
          | _ => -1
        let fs := env.features stats q
        out := out.push ("\t".intercalate ([toString s.index, db.asserts[s.index]!.name, toString prop.parent,
          if q == p then "1" else "0",
          toString a, toString kids.size] ++ (fs.map featureText).toList))
    return out

/-- The rows of statement `i` of the file, a theorem, along its known proof: none for a
proof the skeleton reader leaves out (a shared conversion). With `negatives` 0, every
variant of a node. -/
def datasetRows (db : Db) (index : Index Nat) (limits : Limits) (uses : Uses) (stats : SymbolStats)
    (negatives : Nat) (i : Nat) : IO (Option (Array String)) := do
  match db.skeleton db.file.stmts[i]! with
  | .error _ | .ok none => return none
  | .ok (some skel) => return some (← datasetRowsOf db index limits uses stats negatives i skel)

end Whitehead.Prove
