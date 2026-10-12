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
  let env := (← (expandHyp 0).run (Env.init db index task)).2
  let convs := env.props.filterMap fun p =>
    match p.step with
    | .conv t pos unfold => some (db.terms[t]!.name, pos, unfold)
    | .assertion _ => none
  checkEq "defs: the goal is expanded by its unfoldings and its folding (<-> is a def here too)"
    convs #[("wb", 0, true), ("wa", 1, true), ("wa", 4, false)]
  -- the unfolding node binds the def's arguments, the folding one its dummies too
  -- (a candidate keeps its raw unifier until it is expanded; `splitProp` splits it)
  let unfoldAt := (env.props.findIdx? fun p => p.step == .conv (term "wa") 1 true).getD 0
  let split := (← (splitProp unfoldAt).run env).2
  checkEq "defs: a candidate is split when it is expanded" (env.props[unfoldAt]!.unif.isSome, split.props[unfoldAt]!.unif.isSome)
    (true, false)
  let unfoldNode := split.props[unfoldAt]!
  checkEq "defs: the arguments of the def are bound by unification"
    (unfoldNode.rule.vars.map fun v => db.showExp (unfoldNode.outer.lookupD v) #["ph", "ps"])
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
  let (rows, found') ← searchAll db { limits := { maxProps := 10000, maxMs := 20000 } } fun _ => pure ()
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
  checkEq "defs: the skeleton of df_an: Conv, Cong into the right side of <->, a fold there"
    (skeletonOf "df_an") "(conv_wff biid (cong'_wb_1 refl_wff (fold'_wa refl_wff)))"
  checkEq "defs: the skeleton of bi1, an unfolding in a premise of ax_mp" (skeletonOf "bi1")
    "(ax_mp (syl ax_3 ax_1) (conv_wff con1 (cong'_wi_1 refl_wff (cong'_wi_0 (unfold'_wb refl_wff) refl_wff))))"
  checkEq "defs: the skeleton of df_eu, with a dummy" (skeletonOf "df_eu")
    "(conv_wff biid (cong'_wb_1 refl_wff (fold'_weu refl_wff)))"
  -- the conversion rules
  let rule (name : String) : Option Assertion := db.asserts.find? (·.name == name)
  checkEq "defs: the rule conv_wff" ((rule "conv_wff").map fun r => (r.hyps.map (db.showExp ·), db.showExp r.concl))
    (some (#["v1", "(≡'wff v0 v1)"], "v0"))
  checkEq "defs: unfold_weu keeps its dummy apart from the arguments"
    ((rule "unfold_weu").map fun r => (r.hyps.map (db.showExp ·), db.showExp r.concl, r.disjs))
    (some (#["(≡wff (wex v2 (wal v0 (wb v1 (weq v0 v2)))) v3)"], "(≡wff (weu v0 v1) v3)", #[(2, 0), (2, 1)]))
  checkEq "defs: a strict cong carries the unfolding in one argument"
    ((rule "cong'_wi_0").map fun r => r.hyps.map (db.showExp ·)) (some #["(≡'wff v0 v1)", "(≡wff v2 v3)"])
  -- a conversion inside what the tree has as a variable: from ph <-> ps and
  -- ~((ph -> ps) -> ~(ps -> ph)) -> ch, prove ch. ax_mp's minor premise is ?A, and the
  -- two premises meet only up to unfolding <-> inside it; the proof found folds the
  -- value into ?A on the side of h0.
  let wi (a b : Exp) : Exp := Exp.mkApp (term "wi") wffTy #[a, b]
  let inVarTask : Task :=
    { limit := id "bi1", sorts := 1, terms := term "wb" + 1,
      consts := (Array.range 3).map fun _ => { ty := wffTy, names := #[] },
      premises := #[Exp.mkApp (term "wb") wffTy #[c 0, c 1], wi (db.unfolded (term "wb") #[c 0, c 1] #[]) (c 2)],
      goal := c 2 }
  let inVar ← searchWith acceptAny (Env.init db index inVarTask) breadthFirst { maxProps := 100000, maxMs := 20000 }
  checkEq "defs: an unfolding inside a variable of the tree is found"
    ((inVar.proof.map (proofText db)).getD "none")
    "(ax_mp (conv_wff h0 (fold'_wb refl_wff)) h1)"
  match inVar.proof with
  | none => pure ()
  | some tree =>
    match emitBody db inVarTask tree with
    | none => check "defs: that proof is emitted" false
    | some cmds =>
      check "defs: and emitted as Conv with its conversion proof"
        ((cmds.filter fun c => match c with | .conv | .cong | .refl | .unfold | .symm => true | _ => false)
          == #[.conv, .symm, .unfold, .symm, .refl])
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

/-- Replay over the full expansion (`oracleAll`, Russell's oracle tactic): every node
gets all its variants, the known proof's are clicked, and with `others` that many other
variants of every node on the way are expanded too, so that their proofs meet the known
one's in the joins. Every proof that reaches the root is checked by the verifier; the
known proof must be among them. -/
def fullReplayTests : TestM Unit := do
  for (path, name) in [(logicPath, "logic"), (defsPath, "defs")] do
    let file ←
      match MmbFile.parse (← IO.FS.readBinFile path) with
      | .ok f => pure f
      | .error e => check s!"full replay {name}: the fixture is read" false e.msg; return
    let db ←
      match Db.ofFile file with
      | .ok db => pure db
      | .error msg => check s!"full replay {name}: the fixture becomes a database" false msg; return
    for others in [some 0, some 4, none] do
      let (stats, bodies) ← replay db { full := true, others } fun _ => pure ()
      check s!"full replay {name}, {others.getD 1000} other variants per node: a proof of every theorem is found"
        (stats.replayed == stats.theorems && stats.failed == 0 && stats.limited == 0)
        s!"{stats.replayed} of {stats.theorems}"
      check s!"full replay {name}, {others.getD 0} other variants per node: no proof at the root is rejected"
        (stats.rejected == 0) s!"{stats.rejected} rejected"
      check s!"full replay {name}, {others.getD 0} other variants per node: the bindings of every expanded candidate make a substitution"
        (stats.counters.badCandidates == 0) s!"{stats.counters.badCandidates} did not"
      if others == none then
        check s!"full replay {name}, all variants: the joins are not trivial, and proofs with one key are merged"
          (stats.counters.tuples > stats.counters.notUnified + stats.replayed && stats.counters.notUnified > 0 &&
            stats.counters.duplicate > 0)
          s!"{stats.counters.tuples} tuples, {stats.counters.notUnified} not unified, {stats.counters.duplicate} merged"
      match MmbFile.parse (file.withBodies bodies) with
      | .error e => check s!"full replay {name}: the file is read" false e.msg
      | .ok f2 =>
        match Whitehead.Verify.checkProofs f2 with
        | .ok () => check s!"full replay {name}, {others.getD 0} others: the file with the replayed bodies is valid" true
        | .error e => check s!"full replay {name}: the file with the replayed bodies is valid" false (e.format f2 "replayed")
    -- in rounds: a first budget of a few nodes stops most theorems at the limit, and
    -- every round gives four times as much, until every proof is found
    let (stats, bodies) ← replay db { full := true, total := 3600000, limits := { maxProps := 4 } } fun _ => pure ()
    check s!"full replay {name} in rounds: every proof is found, after more than one round"
      (stats.replayed == stats.theorems && stats.failed == 0 && stats.limited == 0 && stats.rounds > 1)
      s!"{stats.replayed} of {stats.theorems} in {stats.rounds} rounds, {stats.limited} at a limit"
    match MmbFile.parse (file.withBodies bodies) with
    | .error e => check s!"full replay {name} in rounds: the file is read" false e.msg
    | .ok f2 =>
      match Whitehead.Verify.checkProofs f2 with
      | .ok () => check s!"full replay {name} in rounds: the file with the replayed bodies is valid" true
      | .error e => check s!"full replay {name} in rounds: the file with the replayed bodies is valid" false (e.format f2 "replayed")

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
  check "replay peano: every proof without a shared conversion is reconstructed"
    (stats.replayed + stats.conversions == stats.theorems && stats.failed == 0 && stats.rejected == 0)
    s!"{stats.replayed} replayed, {stats.failed} not, {stats.convInVariable} at a variable, {stats.rejected} rejected"
  match MmbFile.parse (file.withBodies bodies) with
  | .error e => check "replay peano: the file with the new bodies is read" false e.msg
  | .ok f2 =>
    match Whitehead.Verify.checkProofs f2 with
    | .ok () => check "replay peano: the file with the new bodies is valid" true
    | .error e => check "replay peano: the file with the new bodies is valid" false (e.format f2 "replayed")
  IO.println s!"replay peano: {stats.replayed} of {stats.theorems} proofs reconstructed, \
    {stats.conversions} with a shared conversion left out"

end Tests.Prove
