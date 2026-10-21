/-
Tests of the congruence procedure (`Whitehead/Prove/Congr.lean`) on `peano.mmb` of the
corpus: the lemmas the table reads by shape, the plan for a goal, and `follow(congr)`
proving the one-sided congruence lemmas from the two-sided ones and reflexivity.
-/
import Whitehead.Prove.Dsl
import Tests.Prove.Engine

open Whitehead.Mmb Whitehead.Prove

namespace Tests.Prove

partial def showSkeleton (db : Db) : Skeleton → String
  | .hyp i => s!"h{i}"
  | .step a cs => s!"({db.asserts[a]!.name}{cs.foldl (init := "") fun acc c => acc ++ " " ++ showSkeleton db c})"

def congrTests : TestM Unit := do
  let path : System.FilePath := ".tools/corpus/peano.mmb"
  if !(← path.pathExists) then
    skip "congr on peano.mmb" "run scripts/build-corpus.sh"
    return
  let file ← match MmbFile.parse (← IO.FS.readBinFile path) with
    | .ok f => pure f
    | .error e => check "congr: peano is read" false e.msg; return
  let db ← match Db.ofFile file with
    | .ok db => pure db
    | .error msg => check "congr: peano becomes a database" false msg; return
  let tb := CongrTable.ofDb db
  let id (n : String) : Nat := thmId db n
  let term (n : String) : Nat := (db.terms.findIdx? (·.name == n)).getD 1000000
  let lemmas (t rel : String) (ded : Bool) : Array CongrLemma := tb.lemmas.getD (term t, term rel, ded) #[]
  check "congr: the table reads peano's deduction-form congruences of `or` under `iff`"
    (let ls := (lemmas "or" "iff" true).map (·.id); ls.contains (id "oreqd") && ls.contains (id "oreq1d") && ls.contains (id "oreq2d"))
    s!"{(lemmas "or" "iff" true).map fun l => db.asserts[l.id]!.name}"
  checkEq "congr: oreq1d rewrites the first argument, oreqd both"
    (#["oreq1d", "oreqd"].map fun n => ((lemmas "or" "iff" true).find? (·.id == id n)).map fun l => (l.positions.map (·.isSome), l.hypPos))
    #[some (#[true, false], #[0]), some (#[true, true], #[0, 1])]
  checkEq "congr: the reflexivity lemmas, by relation and form"
    #[tb.refl[(term "eq", false)]?, tb.refl[(term "eq", true)]?, tb.refl[(term "iff", true)]?]
    #[some (id "eqid"), some (id "eqidd"), some (id "biidd")]
  checkEq "congr: the connective of the deduction form" tb.connective (some (term "im"))
  -- the plan for oreq1d's own statement, from the lemmas before it: oreqd, its first
  -- premise open (the hypothesis), its second by reflexivity
  let task := db.task (id "oreq1d")
  checkEq "congr: the plan for oreq1d's statement" ((tb.planGoal (id "oreq1d") task.goal).map (showSkeleton db))
    (some "(oreqd h0 (biidd))")
  check "congr: no plan for a goal that is not a congruence" (tb.planGoal (id "oreq1d") (db.task (id "eqcomd")).goal).isNone
  -- in a search: follow(congr) proves the one-sided lemmas from the two-sided ones
  let vc := Whitehead.Verify.Ctx.ofFile file
  let rails : Thunk Rails := Thunk.mk fun _ => Rails.ofDb db
  let uses := Uses.ofFile file db.asserts.size
  for name in ["oreq1d", "oreq2d", "ifpeq1d", "imeq2d"] do
    let ctx : Dsl.Ctx := { db, thm := id name, rails := some rails }
    match Dsl.parseTactic ctx "follow(congr, at=root)" with
    | .error e => check s!"congr: follow(congr) proves {name}" false e.msg
    | .ok t =>
      let r ← search vc { Env.init db db.index (db.task (id name)) with uses } t.strategy { maxProps := 100000, maxMs := 10000 }
      check s!"congr: follow(congr) proves {name} from the two-sided lemma and reflexivity" (r.ending == .proved)
        s!"{r.env.counters.expanded} expanded"
  -- and nothing else: on a theorem that is no congruence it expands nothing
  let ctx : Dsl.Ctx := { db, thm := id "eqcomd", rails := some rails }
  match Dsl.parseTactic ctx "follow(congr, at=root)" with
  | .error e => check "congr: nothing at a goal that is no congruence" false e.msg
  | .ok t =>
    let r ← search vc { Env.init db db.index (db.task (id "eqcomd")) with uses } t.strategy { maxProps := 100000, maxMs := 10000 }
    check "congr: nothing at a goal that is no congruence" (r.ending == .exhausted && r.env.counters.expanded == 0)

end Tests.Prove
