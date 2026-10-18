/-
Tests of the data of the learned ranking layer (`Prove/Features.lean`,
`Prove/Dataset.lean`) on `tests/fixtures/prove/logic.mmb`: a row for each variant kept, a
feature for each name, one known variant a goal node of the path, the draw of the others
fixed, and the counts of proofs only those before the theorem.
-/
import Whitehead.Prove.Dataset
import Whitehead.Prove.Model
import Whitehead.Prove.Dsl
import Tests.Prove.Engine

open Whitehead.Mmb Whitehead.Prove

namespace Tests.Prove

def datasetTests : TestM Unit := do
  let bytes ← IO.FS.readBinFile logicPath
  let some file := MmbFile.parse bytes |>.toOption | check "dataset: the fixture is read" false; return
  let some db := Db.ofFile file |>.toOption | check "dataset: the fixture becomes a database" false; return
  let uses := Uses.ofFile file db.asserts.size
  let stats := SymbolStats.ofDb db
  let id := thmId db
  let some i := (Array.range file.stmts.size).find? (file.stmts[·]!.index == id "syl")
    | check "dataset: syl is a statement" false; return
  let rowsOf (negatives : Nat) : IO (Array (Array String)) := do
    let r ← datasetRows db db.index {} uses stats negatives i
    return ((r.getD #[]).map fun l => (l.splitOn "\t").toArray)
  let all ← rowsOf 0
  let few ← rowsOf 1
  let header := (datasetHeader.splitOn "\t").toArray
  check "dataset: a row has a field for each column" (!all.isEmpty && all.all (·.size == header.size))
    s!"{all.size} rows"
  checkEq "dataset: a column for each feature" (header.size - 6) featureNames.size
  -- the goal nodes of the path, each with one known variant
  let nodes := all.foldl (init := (#[] : Array String)) fun acc r => if acc.contains r[2]! then acc else acc.push r[2]!
  check "dataset: one known variant at each goal node of the path"
    (nodes.all fun n => (all.filter fun r => r[2]! == n && r[3]! == "1").size == 1) s!"{nodes}"
  check "dataset: with every variant, a row for each, as the node counts them"
    (nodes.all fun n => let rs := all.filter (·[2]! == n); rs.all fun r => r[5]! == toString rs.size)
  check "dataset: with one negative, two rows a node at most, the known one among them"
    (nodes.all fun n => let rs := few.filter (·[2]! == n); rs.size ≤ 2 && rs.any (·[3]! == "1"))
  checkEq "dataset: the draw is fixed" (← rowsOf 1) few
  -- the counts of proofs: none before the first theorem
  let some j := (Array.range file.stmts.size).find? (file.stmts[·]!.index == id "a1i") | return
  let first ← datasetRows db db.index {} uses stats 0 j
  let usesCol := (header.findIdx? (· == "uses_log")).getD 0
  check "dataset: before the first proof, nothing is used"
    (((first.getD #[]).map fun l => ((l.splitOn "\t").toArray)[usesCol]!).all (· == "0"))

/-- The models: the numbers of JSON, a tree of LightGBM's dump, a linear model, and a
model of other features refused. -/
def modelTests : TestM Unit := do
  checkEq "model: numbers" (#["3", "-0.25", "2.5E3", "1e-35", "x", "1e", ""].map fun t => (parseFloat t).map toString)
    #[some "3.000000", some "-0.250000", some "2500.000000", some (toString (1e-35 : Float)), none, none, none]
  let names := Whitehead.Json.arr (featureNames.map Whitehead.Json.str)
  let treeText := s!"\{\"feature_names\": {names.compress}, \"tree_info\": [\{\"tree_structure\": \{\"split_feature\": 1, \"threshold\": 0.5, \"decision_type\": \"<=\", \"default_left\": true, \"missing_type\": \"None\", \"left_child\": \{\"leaf_value\": -1}, \"right_child\": \{\"split_feature\": 2, \"threshold\": 1.0000000180025095e-35, \"decision_type\": \"<=\", \"default_left\": false, \"missing_type\": \"Zero\", \"left_child\": \{\"leaf_value\": 2}, \"right_child\": \{\"leaf_value\": 3.5}}}}, \{\"tree_structure\": \{\"leaf_value\": 0.25}}]}"
  let x (a b : Float) : Array Float := (Array.replicate featureNames.size 0).set! 1 a |>.set! 2 b
  match Whitehead.Json.parse treeText with
  | .error e => check "model: the trees are read" false e.msg
  | .ok j =>
    match Model.ofJson j with
    | .error e => check "model: the trees are read" false e
    | .ok m =>
      checkEq "model: trees, left, right, a zero taken as missing"
        (#[m.score (x 0 0), m.score (x 1 5), m.score (x 1 0)]) #[-0.75, 3.75, 3.75]
  let w := Whitehead.Json.arr ((Array.range featureNames.size).map fun i => .int (if i == 1 then 2 else 0))
  let ones := Whitehead.Json.arr (featureNames.map fun _ => .int 1)
  let zeros := Whitehead.Json.arr (featureNames.map fun _ => .int 0)
  match Model.ofJson (.obj #[("features", names), ("mean", zeros), ("scale", ones), ("weights", w)]) with
  | .error e => check "model: a linear model is read" false e
  | .ok m => checkEq "model: linear" (m.score (x 3 0)) 6
  match Model.ofJson (.obj #[("features", .arr #[.str "other"]), ("mean", zeros), ("scale", ones), ("weights", w)]) with
  | .error e => check "model: other features are refused" (contains e "features") e
  | .ok _ => check "model: other features are refused" false
  -- in a search: the variants ordered by a model, here by how much their assertion is used
  let bytes ← IO.FS.readBinFile logicPath
  let some file := MmbFile.parse bytes |>.toOption | return
  let some db := Db.ofFile file |>.toOption | return
  let vc := Whitehead.Verify.Ctx.ofFile file
  let usesW := Whitehead.Json.arr ((Array.range featureNames.size).map fun i =>
    .int (if featureNames[i]! == "uses_log" then 1 else 0))
  match Model.ofJson (.obj #[("features", names), ("mean", zeros), ("scale", ones), ("weights", usesW)]) with
  | .error e => check "model: a model in a search" false e
  | .ok m =>
    let ctx : Dsl.Ctx := { db, model := some m }
    checkEq "model: by=model needs a model" ((Dsl.parseTactic { db } "search(depth(by=model, width=1))").toOption.isNone) true
    match Dsl.parseTactic ctx "search(depth(by=model, width=1))" with
    | .error e => check "model: a model in a search" false e.msg
    | .ok t =>
      let uses := Uses.ofFile file db.asserts.size
      let r ← search vc { Env.init db db.index (db.task (thmId db "syl")) with uses } t.strategy { maxProps := 100000 }
      check "model: a search ordered by a model proves syl" (r.ending == .proved)

end Tests.Prove
