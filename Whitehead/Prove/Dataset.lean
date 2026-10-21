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

The data of the value of goals is another: the goal nodes of the tree that a search
grew, each labelled by whether the search proved it (`goalRows`), as GPT-f learns its
value from its own searches.
-/
import Whitehead.Prove.Features
import Whitehead.Prove.Measure
import Whitehead.Prove.Prior

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

/-- The rows of statement `i` of the file, a theorem, along the proof `skel`; `prior` is
the theorem's (`Prior.query`). -/
def datasetRowsOf (db : Db) (index : Index Nat) (limits : Limits) (uses : Uses) (stats : SymbolStats)
    (negatives : Nat) (i : Nat) (skel : Skeleton) (prior : Std.HashMap Nat Float := {}) : IO (Array String) := do
    let s := db.file.stmts[i]!
    let env := { Env.init db index (db.task s.index) with uses, prior }
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
    (negatives : Nat) (i : Nat) (prior : Std.HashMap Nat Float := {}) : IO (Option (Array String)) := do
  match db.skeleton db.file.stmts[i]! with
  | .error _ | .ok none => return none
  | .ok (some skel) => return some (← datasetRowsOf db index limits uses stats negatives i skel prior)

/-- The header of the goal rows: the theorem by number and name, the goal node, the label
(1 if the search proved it), the assertion whose premise the goal is (-1 for the root or
an unfolding), the goal's number of variants, and the goal features. -/
def goalHeader : String :=
  "\t".intercalate (["thm", "name", "node", "label", "assertion", "variants"] ++ goalFeatureNames.toList)

/-- The rows of the goal nodes of `env`, the tree of a search on theorem `thm`: the root,
labelled `proved` (the search's verdict: a proof at the root may be one the verifier
rejects), and the premises of the steps expanded, each labelled by whether it is proved.
A goal with metavariables is proved only when its step is too: a proof of it binds them,
and the binding must suit the step's other goals. A premise of the theorem that unifies
with `im _G ?x` proves it at once, and taken alone such goals were all proved, and the
steps that make them looked free (mm0's congruences, `docs/DESIGN.md`, step 4). At most
`cap` of them (0 for all), drawn by the node. -/
def goalRows (env : Env) (stats : SymbolStats) (thm : Nat) (proved : Bool) (cap : Nat) : Array String :=
  let ti := env.taskInfo stats
  let nodes := (Array.range env.hyps.size).filter fun h => h == 0 || env.hyps[h]!.parent.isSome
  let chosen := if cap == 0 || nodes.size ≤ cap then nodes
    else ((nodes.qsort fun a b => mixHash thm a < mixHash thm b).extract 0 cap).qsort (· < ·)
  chosen.map fun h =>
    let g := env.hyps[h]!
    let a : Int := match g.parent with
      | some q => match env.props[q]!.step with
        | .assertion id => if (env.db.asserts[id]?.bind (·.pseudo)).isNone then id else -1
        | _ => -1
      | none => -1
    let label := if h == 0 then proved
      else !g.proofs.isEmpty && (!g.expr.hasVars || g.parent.any fun q => !env.props[q]!.proofs.isEmpty)
    let siblings := match g.parent with
      | some q => env.props[q]!.children.filterMap fun c => if c == h then none else some env.hyps[c]!.expr
      | none => #[]
    "\t".intercalate ([toString thm, env.db.asserts[thm]!.name, toString h, if label then "1" else "0",
      toString a, toString g.children.size] ++
      ((env.goalFeatures stats ti g.expr (env.goalDepth h) siblings).map featureText).toList)

end Whitehead.Prove
