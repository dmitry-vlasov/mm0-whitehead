/-
Tests of unfolding on `tests/fixtures/prove/defs.mmb` (a copy of `examples/set.mm1` of
the MM0 repository, compiled by `mm0-rs`): the values of the defs in the database, the
rule made for an unfolding, the expansion of a goal by its unfoldings and foldings,
search with unfolding, emission as `Conv`, and replay of the proofs with conversions.
-/
import Whitehead.Prove.Replay
import Tests.Harness
import Tests.Prove.Engine

open Whitehead.Mmb Whitehead.Prove

namespace Tests.Prove

def defsPath : System.FilePath := "tests/fixtures/prove/defs.mmb"

def defsTests : TestM Unit := do
  let bytes ← IO.FS.readBinFile defsPath
  let file ←
    match MmbFile.parse bytes with
    | .ok f => pure f
    | .error e => check "defs: the fixture is read" false e.msg; return
  let db ←
    match Db.ofFile file with
    | .ok db => pure db
    | .error msg => check "defs: the fixture becomes a database" false msg; return
  let vc := Whitehead.Verify.Ctx.ofFile file
  let index := db.index
  let id := thmId db
  let term (name : String) : Nat := (db.terms.findIdx? (·.name == name)).getD 0
  -- the database
  checkEq "defs: the defs, in order" (db.defs.map fun t => db.terms[t]!.name)
    #["wb", "wa", "or", "wex", "weu", "sb", "wceq", "cv", "wcel"]
  let value (name : String) : String :=
    match db.terms[term name]!.value with
    | some v => s!"{db.showExp v.expr} dummies {v.dummies.map (Db.varName ∘ Node.varId)}"
    | none => "none"
  checkEq "defs: the value of wb over its arguments" (value "wb") "(wn (wi (wi v0 v1) (wn (wi v1 v0)))) dummies #[]"
  checkEq "defs: a dummy is a variable after the arguments, a name" (value "weu")
    "(wex v2 (wal v0 (wb v1 (weq v0 v2)))) dummies #[v2]"
  check "defs: a dummy has the name type of its sort" (Ty.isName (Node.ty (db.terms[term "weu"]!.value.get!.dummies[0]!)))
  let wffTy := Ty.mk 0 false
  let c (k : Nat) : Exp := ⟨#[Node.const k wffTy]⟩
  checkEq "defs: a def unfolded with expressions" (db.showExp (db.unfolded (term "wa") #[c 0, c 1] #[]) #["ph", "ps"])
    "(wn (wi ph (wn ps)))"
  -- the rule for an unfolding: df_an is `(ph /\ ps) <-> ~(ph -> ~ps)`
  let task := db.task (id "df_an")
  checkEq "defs: the goal of df_an" (db.showExp task.goal #["ph", "ps"]) "(wb (wa ph ps) (wn (wi ph (wn ps))))"
  match convRule db task.goal (term "wa") 1 true with
  | none => check "defs: the rule for unfolding wa in the goal" false
  | some r =>
    checkEq "defs: the rule for unfolding wa in the goal: conclusion and premise"
      (db.showExp r.concl #["ph", "ps"], r.hyps.map (db.showExp · #["ph", "ps"]), r.disjs)
      ("(wb (wa v0 v1) (wn (wi ph (wn ps))))", #["(wb (wn (wi v0 (wn v1))) (wn (wi ph (wn ps))))"], #[])
  match convRule db task.goal (term "wa") 4 false with
  | none => check "defs: the rule for folding wa in the goal" false
  | some r =>
    checkEq "defs: the rule for folding: the value is the conclusion, the def the premise"
      (db.showExp r.concl #["ph", "ps"], r.hyps.map (db.showExp · #["ph", "ps"]))
      ("(wb (wa ph ps) (wn (wi v0 (wn v1))))", #["(wb (wa ph ps) (wa v0 v1))"])
  -- the expansion of the goal has both, each once
  let env := ((expandHyp 0).run (Env.init db index task)).2
  let convs := env.props.filterMap fun p =>
    match p.step with
    | .conv t pos unfold => some (db.terms[t]!.name, pos, unfold)
    | .assertion _ => none
  checkEq "defs: the goal is expanded by its unfoldings and its folding (<-> is a def here too)"
    convs #[("wb", 0, true), ("wa", 1, true), ("wa", 4, false)]
  -- the unfolding node binds the def's arguments, the folding one its dummies too
  let unfoldNode := env.props.find? fun p => p.step == .conv (term "wa") 1 true
  checkEq "defs: the arguments of the def are bound by unification"
    ((unfoldNode.map fun p => p.rule.vars.map fun v => db.showExp (p.outer.lookupD v) #["ph", "ps"]).getD #[])
    #["ph", "ps"]
  -- search: df_an from biid and the unfolding; the body is verified
  let limits : Limits := { maxProps := 5000, maxMs := 20000 }
  let prove (name : String) : IO Result := search vc (Env.init db index (db.task (id name))) breadthFirst limits
  let found (name : String) : IO String := do
    let r ← prove name
    return match r.proof with
      | some t => proofText db t
      | none => s!"none ({r.rejected} rejected: {r.rejection})"
  checkEq "defs: df_an is proved by unfolding" (← found "df_an") "(unfold wa@#[0] biid)"
  checkEq "defs: df_or" (← found "df_or") "(unfold or@#[0] biid)"
  -- a def with a bound argument and a dummy: the dummy becomes the theorem's y
  let eu ← prove "df_eu"
  checkEq "defs: df_eu, with a dummy (folded: the first found)" ((eu.proof.map (proofText db)).getD "none") "(fold weu@#[1] biid)"
  check "defs: the dummy is the bound variable of the theorem, not a new name"
    (match eu.proof with
      | some (.conv _ _ _ _ dummies _) => dummies.size == 1 && Node.isConst dummies[0]!.nodes[0]!
      | _ => false)
  checkEq "defs: df_sb, with a bound argument and a dummy" ((← found "df_sb")) "(fold sb@#[1] biid)"
  -- a theorem proved by an unfolding deeper in the goal: bi1 is `(ph <-> ps) -> ph -> ps`
  let bi1 ← search vc (Env.init db index (db.task (id "bi1"))) breadthFirst { maxProps := 50000, maxMs := 20000 }
  checkEq "defs: bi1 is proved, the unfolding being where the goal's structure has got to"
    ((bi1.proof.map (proofText db)).getD "none") "(ax_mp (syl ax_3 ax_1) (unfold wb@#[1, 0] con1))"
  -- eqcid is `A = A`: the def wceq has a dummy, which is left as a new name
  let eqcid ← search vc (Env.init db index (db.task (id "eqcid"))) breadthFirst { maxProps := 50000, maxMs := 20000 }
  check "defs: eqcid is proved, the dummy of wceq being a new name"
    (eqcid.ending == .proved && (match eqcid.proof with
      | some (.conv _ _ true _ dummies _) => dummies.size == 1 && dummies[0]!.isVar
      | _ => false))
    ((eqcid.proof.map (proofText db)).getD "none")
  -- every proof found is a proof: the bodies make a valid file
  let (rows, found') ← searchAll db { limits := { maxProps := 3000, maxMs := 20000 } } fun _ => pure ()
  let proved := (rows.filter (·.ending == .proved)).size
  check "defs: most of the fixture is proved from scratch" (proved ≥ 20) s!"{proved} of {rows.size}"
  check "defs: no proof is rejected by the verifier" (rows.all (·.rejected == 0))
  match MmbFile.parse (file.withBodies found') with
  | .error e => check "defs: the file with the proofs found is read" false e.msg
  | .ok f2 =>
    match Whitehead.Verify.checkProofs f2 with
    | .ok () => check "defs: the file with the proofs found is valid" true
    | .error e => check "defs: the file with the proofs found is valid" false (e.format f2 "searched")
  -- the proofs of the file as skeletons: a conversion is read as unfoldings with their
  -- places, from the goal's side first
  let skeletonOf (name : String) : String :=
    match file.stmts.find? fun s => (match s.kind with | .thm _ => true | _ => false) && s.index == id name with
    | some s =>
      match db.skeleton s with
      | .ok (some sk) => skeletonText db sk
      | .ok none => "shared conversion"
      | .error msg => msg
    | none => "no such theorem"
  checkEq "defs: the skeleton of df_an: the file instantiates biid with the def, and folds the goal's value"
    (skeletonOf "df_an") "(fold wa@#[1] biid)"
  checkEq "defs: the skeleton of bi1, an unfolding in a premise of ax_mp" (skeletonOf "bi1")
    "(ax_mp (syl ax_3 ax_1) (unfold wb@#[1, 0] con1))"
  checkEq "defs: the skeleton of df_eu, with a dummy" (skeletonOf "df_eu") "(fold weu@#[1] biid)"
  -- replay: every proof of the fixture, with its conversions, is reconstructed
  let (stats, bodies) ← replay db {} fun _ => pure ()
  checkEq "defs: every proof of the fixture is replayed" (stats.replayed, stats.failed, stats.conversions) (26, 0, 0)
  checkEq "defs: replay, the same number of steps" stats.stepsOut stats.stepsIn
  match MmbFile.parse (file.withBodies bodies) with
  | .error e => check "defs: the file with the replayed bodies is read" false e.msg
  | .ok f2 =>
    match Whitehead.Verify.checkProofs f2 with
    | .ok () => check "defs: the file with the replayed bodies is valid" true
    | .error e => check "defs: the file with the replayed bodies is valid" false (e.format f2 "replayed")

/-- The replay of `peano.mmb` of the corpus, whose proofs unfold definitions: what is
replayed, and what is not and why. -/
def replayDefsCorpusTests : TestM Unit := do
  let path : System.FilePath := ".tools/corpus/peano.mmb"
  if !(← path.pathExists) then
    skip "replay of peano.mmb" "run scripts/build-corpus.sh"
    return
  let file ←
    match MmbFile.parse (← IO.FS.readBinFile path) with
    | .ok f => pure f
    | .error e => check "replay peano: the file is read" false e.msg; return
  let db ←
    match Db.ofFile file with
    | .ok db => pure db
    | .error msg => check "replay peano: the file becomes a database" false msg; return
  let (stats, bodies) ← replay db {} fun _ => pure ()
  check "replay peano: the proofs with conversions at places the tree has are reconstructed"
    (stats.replayed ≥ 2400 && stats.failed == stats.convInVariable && stats.rejected == 0)
    s!"{stats.replayed} replayed, {stats.failed} not, {stats.convInVariable} at a variable, {stats.rejected} rejected"
  match MmbFile.parse (file.withBodies bodies) with
  | .error e => check "replay peano: the file with the new bodies is read" false e.msg
  | .ok f2 =>
    match Whitehead.Verify.checkProofs f2 with
    | .ok () => check "replay peano: the file with the new bodies is valid" true
    | .error e => check "replay peano: the file with the new bodies is valid" false (e.format f2 "replayed")
  IO.println s!"replay peano: {stats.replayed} of {stats.theorems} proofs reconstructed, {stats.failed} with an \
    unfolding where the tree has a variable, {stats.conversions} with a shared conversion left out"

end Tests.Prove
