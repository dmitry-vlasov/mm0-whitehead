/-
Tests of the data of the learned ranking layer (`Prove/Features.lean`,
`Prove/Dataset.lean`) on `tests/fixtures/prove/logic.mmb`: a row for each variant kept, a
feature for each name, one known variant a goal node of the path, the draw of the others
fixed, the counts of proofs only those before the theorem, and the rows along a proof
that the search found.
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
  -- along a proof the search finds (expert iteration): its skeleton is followed, and a
  -- proof of the known shape gives the known proof's rows
  let vc := Whitehead.Verify.Ctx.ofFile file
  let r ← searchWith (accept vc) { Env.init db db.index (db.task (id "syl")) with uses } breadthFirst
    { maxProps := 100000 }
  match r.proof.bind ProofTree.skeleton?, db.skeleton file.stmts[i]! with
  | some sk, .ok (some known) =>
    let found := (← datasetRowsOf db db.index {} uses stats 0 i sk).map fun l => (l.splitOn "\t").toArray
    let fnodes := found.foldl (init := (#[] : Array String)) fun acc r => if acc.contains r[2]! then acc else acc.push r[2]!
    check "dataset: along a found proof, one known variant at each goal node"
      (!fnodes.isEmpty && fnodes.all fun n => (found.filter fun r => r[2]! == n && r[3]! == "1").size == 1)
    if r.proof.any (sameShape · known) then checkEq "dataset: a found proof of the known shape, the known rows" found all
  | _, _ => check "dataset: the search proves syl, a proof of assertions" false
  -- the goal rows of the search's tree (the value of goals): a row for each goal node,
  -- the root's label the search's verdict, the others whether the node has a proof
  let goals := (goalRows r.env stats (id "syl") r.proof.isSome 0).map fun l => (l.splitOn "\t").toArray
  let gheader := (goalHeader.splitOn "\t").toArray
  checkEq "goal rows: a column for each goal feature" (gheader.size - 6) goalFeatureNames.size
  check "goal rows: a row for each goal node of the backward tree, with a field for each column"
    (goals.size == (r.env.hyps.filter fun g => g.parent.isSome).size + 1 && goals.all (·.size == gheader.size))
    s!"{goals.size} rows"
  check "goal rows: the root proved, as the search says" (goals[0]?.any fun g => g[2]! == "0" && g[3]! == "1")
  -- with metavariables, only when its step is proved too
  let provedGoal (h : Nat) : Bool :=
    let g := r.env.hyps[h]!
    !g.proofs.isEmpty && (!g.expr.hasVars || g.parent.any fun q => !r.env.props[q]!.proofs.isEmpty)
  check "goal rows: a goal is proved when its node has a proof, and its step too if it has metavariables"
    (goals.all fun g => g[2]! == "0" || (g[3]! == "1") == provedGoal g[2]!.toNat!)
  check "goal rows: proved goals and others" (goals.any (·[3]! == "0") && goals.any (·[3]! == "1"))
  checkEq "goal rows: at most cap of them, the draw fixed"
    ((goalRows r.env stats (id "syl") true 5).size, goalRows r.env stats (id "syl") true 5)
    (5, goalRows r.env stats (id "syl") true 5)
  -- the features of a variant's new goals are those of the goal nodes its expansion makes:
  -- the cost reads them before, the data after
  let env := r.env
  let ti := env.taskInfo stats
  let leaves := ((Array.range env.props.size).filter fun p =>
    !env.props[p]!.expanded && env.props[p]!.rule.hyps.size > 0).extract 0 20
  let mut same := true
  for p in leaves do
    let depth := env.goalDepth env.props[p]!.parent + 1
    let goals := (env.propView p).goals.get
    let others (xs : Array Exp) (i : Nat) : Array Exp := (Array.range xs.size).filterMap fun j => if j == i then none else some xs[j]!
    let before := (Array.range goals.size).map fun i => env.goalFeatures stats ti goals[i]! depth (others goals i)
    let ((), after) ← (proveProp p).run env
    let kids := after.props[p]!.children.map fun h => after.hyps[h]!.expr
    let made := (Array.range kids.size).map fun i => after.goalFeatures stats ti kids[i]! (after.goalDepth after.props[p]!.children[i]!) (others kids i)
    if made != before then same := false
  check s!"goal rows: the features of the new goals of {leaves.size} variants, before and after their expansion"
    (leaves.size > 5 && same)
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
      -- a value of goals: of the goal features, its score the log-odds; in a search's cost
      let gnames := Whitehead.Json.arr (goalFeatureNames.map Whitehead.Json.str)
      let gzeros := Whitehead.Json.arr (goalFeatureNames.map fun _ => .int 0)
      let gones := Whitehead.Json.arr (goalFeatureNames.map fun _ => .int 1)
      let closableW := Whitehead.Json.arr (goalFeatureNames.map fun n => .int (if n == "closable" then 2 else 0))
      let vj := Whitehead.Json.obj #[("features", gnames), ("mean", gzeros), ("scale", gones), ("weights", closableW)]
      check "model: a value is refused for the features of variants" (Model.ofJson vj).toOption.isNone
      match Model.ofJson vj goalFeatureNames with
      | .error e => check "model: a value of goals is read" false e
      | .ok v =>
        let x (closable : Float) := (Array.replicate goalFeatureNames.size 0).set!
          ((goalFeatureNames.findIdx? (· == "closable")).getD 0) closable
        checkEq "model: a value is the probability of the log-odds"
          (#[v.value (x 0), (v.value (x 1) * 1000).round]) #[0.5, 881]
        let text := "search(depth(by=model, width=1, value=2))"
        checkEq "model: value=K needs a value" ((Dsl.parseTactic ctx text).toOption.isNone) true
        checkEq "model: value=K needs a by"
          ((Dsl.parseTactic { ctx with value := some v } "search(depth(value=2))").toOption.isNone) true
        match Dsl.parseTactic { ctx with value := some v } text with
        | .error e => check "model: a value in a search" false e.msg
        | .ok t =>
          let r ← search vc { Env.init db db.index (db.task (thmId db "syl")) with uses } t.strategy { maxProps := 100000 }
          check "model: a search with a value of goals proves syl" (r.ending == .proved)
          match Dsl.parseTactic { ctx with value := some v } "search(depth(by=model, width=1, value=2, absolute=1))" with
          | .error e => check "model: an absolute value in a search" false e.msg
          | .ok t =>
            let r ← search vc { Env.init db db.index (db.task (thmId db "syl")) with uses } t.strategy { maxProps := 100000 }
            check "model: a search with an absolute value of goals proves syl" (r.ending == .proved)
          match Dsl.parseTactic { ctx with value := some v } "search(depth(by=model, width=1, value=2, cap=1))" with
          | .error e => check "model: a capped value in a search" false e.msg
          | .ok t =>
            let r ← search vc { Env.init db db.index (db.task (thmId db "syl")) with uses } t.strategy { maxProps := 100000 }
            check "model: a search with a capped value of goals proves syl" (r.ending == .proved)
          checkEq "model: cap is a parameter of depth"
            ((Dsl.parseTactic { ctx with value := some v } "search(depth(by=model, width=1, value=2, cap=x))").toOption.isNone) true
          -- a two-stage rank: a cheap model orders all the variants, the model the first `top`
          match Dsl.parseTactic { ctx with cheap := ctx.model } "search(depth(by=model, width=1, top=2))" with
          | .error e => check "model: a two-stage rank in a search" false e.msg
          | .ok t =>
            let r ← search vc { Env.init db db.index (db.task (thmId db "syl")) with uses } t.strategy { maxProps := 100000 }
            check "model: a search with a two-stage rank proves syl" (r.ending == .proved)

end Tests.Prove
