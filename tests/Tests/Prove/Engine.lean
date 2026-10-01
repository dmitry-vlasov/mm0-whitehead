/-
Tests of the engine on `tests/fixtures/prove/logic.mmb`, a small deductive system with
propositional axioms, a quantifier and proofs (compiled from `logic.mm1` by `mm0-rs`):
the database, replay of every proof, breadth-first search, the conditions on bound
variables, and what happens to the variables that a proof leaves open.
-/
import Whitehead.Prove.Replay
import Tests.Harness

open Whitehead.Mmb Whitehead.Prove

namespace Tests.Prove

def logicPath : System.FilePath := "tests/fixtures/prove/logic.mmb"

/-- The number of the assertion with this name. -/
def thmId (db : Db) (name : String) : Nat :=
  (db.asserts.findIdx? (·.name == name)).getD 0

partial def skeletonText (db : Db) : Skeleton → String
  | .hyp i => s!"h{i}"
  | .step t children =>
    if children.isEmpty then db.asserts[t]!.name
    else s!"({db.asserts[t]!.name} {" ".intercalate (children.map (skeletonText db)).toList})"

partial def proofText (db : Db) : ProofTree → String
  | .hyp i => s!"h{i}"
  | .step t _ children =>
    if children.isEmpty then db.asserts[t]!.name
    else s!"({db.asserts[t]!.name} {" ".intercalate (children.map (proofText db)).toList})"

def engineTests : TestM Unit := do
  let bytes ← IO.FS.readBinFile logicPath
  let file ←
    match MmbFile.parse bytes with
    | .ok f => pure f
    | .error e => check "engine: the fixture is read" false e.msg; return
  let db ←
    match Db.ofFile file with
    | .ok db => pure db
    | .error msg => check "engine: the fixture becomes a database" false msg; return
  let vc := Whitehead.Verify.Ctx.ofFile file
  let index := db.index
  let id := thmId db
  -- the database
  checkEq "db: assertions" db.asserts.size 24
  checkEq "db: a conclusion" (db.showExp db.asserts[id "ax_2"]!.concl) "(wi (wi v0 (wi v1 v2)) (wi (wi v0 v1) (wi v0 v2)))"
  checkEq "db: hypotheses in the order of the statement"
    (db.asserts[id "mpd"]!.hyps.map (db.showExp ·)) #["(wi v0 v1)", "(wi v0 (wi v1 v2))"]
  checkEq "db: a bound binder is a name" (db.asserts[id "ax_gen"]!.vars.map fun v => Ty.isName (Node.ty v)) #[true, false]
  checkEq "db: ax_5 keeps x apart from ph" db.asserts[id "ax_5"]!.disjs #[(0, 1)]
  checkEq "db: ax_4 lets both depend on x" db.asserts[id "ax_4"]!.disjs #[]
  checkEq "db: two bound binders must differ; the regular one may depend on both"
    db.asserts[id "alcomi"]!.disjs #[(0, 1)]
  checkEq "db: alrimi keeps x apart from ph only" db.asserts[id "alrimi"]!.disjs #[(0, 1)]
  let task := db.task (id "alimi")
  checkEq "task: the variables are constants" (db.showExp task.goal #["x", "ph", "ps"]) "(wi (wal x ph) (wal x ps))"
  checkEq "task: premises" (task.premises.map (db.showExp · #["x", "ph", "ps"])) #["(wi ph ps)"]
  checkEq "task: what each constant depends on" (task.consts.map (·.names)) #[#[0], #[0], #[0]]
  checkEq "task: only what is declared before" (task.limit, task.terms) (id "alimi", 3)
  -- the proofs of the file as trees
  let skeletonOf (name : String) : String :=
    match file.stmts.find? fun s => (match s.kind with | .thm _ => true | _ => false) && s.index == id name with
    | some s =>
      match db.skeleton s with
      | .ok (some sk) => skeletonText db sk
      | .ok none => "conversion"
      | .error msg => msg
    | none => "no such theorem"
  checkEq "skeleton: id" (skeletonOf "id") "(mpd ax_1 ax_1)"
  checkEq "skeleton: hypotheses are leaves" (skeletonOf "mpd") "(ax_mp h0 (ax_mp h1 ax_2))"
  checkEq "skeleton: alrimi" (skeletonOf "alrimi") "(syl (alimi h0) ax_5)"
  -- replay
  let (stats, bodies) ← replay db {} fun _ => pure ()
  checkEq "replay: every proof of the fixture is reconstructed" (stats.replayed, stats.failed) (16, 0)
  checkEq "replay: the same number of steps" stats.stepsOut stats.stepsIn
  check "replay: nothing fails to unify, nothing is rejected"
    (stats.counters.notUnified == 0 && stats.counters.inconsistent == 0 && stats.rejected == 0)
  match MmbFile.parse (file.withBodies bodies) with
  | .error e => check "replay: the file with the new bodies is read" false e.msg
  | .ok f2 =>
    match Whitehead.Verify.checkProofs f2 with
    | .ok () => check "replay: the file with the new bodies is valid" true
    | .error e => check "replay: the file with the new bodies is valid" false (e.format f2 "replayed")
  -- search
  let limits : Limits := { maxProps := 5000, maxMs := 20000 }
  let prove (name : String) : IO Result := search vc (Env.init db index (db.task (id name))) breadthFirst limits
  let found (name : String) : IO String := do
    let r ← prove name
    return match r.proof with
      | some t => proofText db t
      | none => "none"
  checkEq "search: a1i" (← found "a1i") "(ax_mp h0 ax_1)"
  checkEq "search: id, as in the file" (← found "id") "(mpd ax_1 ax_1)"
  checkEq "search: mpd, shorter than in the file" (← found "mpd") "(ax_mp h0 (a2i h1))"
  checkEq "search: syl" (← found "syl") "(mpd h1 (a1i h0))"
  checkEq "search: under a quantifier" (← found "alimi") "(ax_mp (ax_gen h0) ax_4)"
  checkEq "search: two bound variables" (← found "alcomi") "(ax_gen (ax_gen h0))"
  checkEq "search: what is provable without the variable needs no dummy" (← found "dummy") "id"
  let alrimi ← prove "alrimi"
  checkEq "search: alrimi" ((alrimi.proof.map (proofText db)).getD "none") "(syl (alimi h0) ax_5)"
  check "search: a proof whose condition on a bound variable fails late is dropped by the verifier"
    (alrimi.rejected == 1) s!"{alrimi.rejected} rejected"
  let con1 ← search vc (Env.init db index (db.task (id "con1"))) breadthFirst { maxProps := 2000 }
  check "search: the limit ends a search" (con1.ending == .limit && con1.proof.isNone)
  -- every proof found is a proof: the bodies make a valid file
  let (rows, found') ← searchAll db { limits := { maxProps := 3000, maxMs := 20000 } } fun _ => pure ()
  let proved := (rows.filter (·.ending == .proved)).size
  check "search: most of the fixture is proved from scratch" (proved ≥ 13) s!"{proved} of {rows.size}"
  check "search: no proof found is longer than the one in the file"
    (rows.all fun r => r.ending != .proved || r.steps ≤ r.knownSteps)
  match MmbFile.parse (file.withBodies found') with
  | .error e => check "search: the file with the proofs found is read" false e.msg
  | .ok f2 =>
    match Whitehead.Verify.checkProofs f2 with
    | .ok () => check "search: the file with the proofs found is valid" true
    | .error e => check "search: the file with the proofs found is valid" false (e.format f2 "searched")
  -- a goal with a variable to be found: from ph and ph -> ps, something of the shape
  -- `?q -> ps`. Constants 0 and 1 are ph and ps; the variable is the first fresh one.
  let wffTy := Ty.mk 0 false
  let c (k : Nat) : Exp := ⟨#[Node.const k wffTy]⟩
  let q : Exp := Exp.ofVar (Node.var freshBase wffTy)
  let wi (a b : Exp) : Exp := Exp.mkApp 0 wffTy #[a, b]
  let answerTask : Task :=
    { limit := id "syl" + 1, sorts := 1, terms := 2,
      consts := #[{ ty := wffTy, names := #[] }, { ty := wffTy, names := #[] }],
      premises := #[c 0, wi (c 0) (c 1)], goal := wi q (c 1) }
  let answerEnv := { Env.init db index answerTask with fresh := freshBase + 1 }
  let answered ← searchWith acceptAny answerEnv breadthFirst { maxProps := 5000 }
  checkEq "answer: a goal with a variable is proved, and the variable found"
    ((answered.answer.map (db.showExp · #["ph", "ps"])).getD "none") "(wi ps ps)"
  checkEq "answer: the first proof, breadth first, is the shortest way to such a goal"
    ((answered.proof.map (proofText db)).getD "none") "id"
  -- without `id` and what follows it, a premise is needed: from ph, by ax_3,
  -- (~ps -> ~ph) -> ps
  let earlier ← searchWith acceptAny { answerEnv with task := { answerTask with limit := id "id" } }
    breadthFirst { maxProps := 5000 }
  checkEq "answer: another answer when less may be used"
    ((earlier.answer.map (db.showExp · #["ph", "ps"])).getD "none", (earlier.proof.map (proofText db)).getD "none")
    ("(wi (wi (wn ps) (wn ph)) ps)", "(mpd (a1i h0) ax_3)")
  -- the condition on bound variables, on an application of ax_5 in the task of alimi,
  -- whose constants are x, ph and ps, the last two depending on x
  let env := Env.init db index task
  let ax5 := db.asserts[id "ax_5"]!
  let cx : Exp := ⟨#[Node.const 0 task.consts[0]!.ty]⟩
  let cph : Exp := ⟨#[Node.const 1 task.consts[1]!.ty]⟩
  let mvar : Exp := Exp.ofVar (Node.var freshBase (Ty.mk 0 false))
  let name' : Exp := Exp.ofVar (Node.var (freshBase + 1) (Ty.mk 1 true))
  let applied (x ph : Exp) : PropNode :=
    { assertion := ax5.id, parent := 0, sub := {},
      outer := { map := (({} : Std.HashMap Nat SubExp).insert 0 (SubExp.mk' ax5.vars[0]! x)).insert 1
                  (SubExp.mk' ax5.vars[1]! ph) } }
  check "disjoint: x given for x, and ph, which depends on x: violated"
    (!checkDisjs env (applied cx cph) {})
  check "disjoint: x, and a variable that may still become anything: open"
    (checkDisjs env (applied cx mvar) {})
  check "disjoint: the same, once the variable is ph: violated"
    (!checkDisjs env (applied cx mvar) (Subst.single mvar.nodes[0]! cph))
  check "disjoint: a new name, and ph: open, the name can be a dummy"
    (checkDisjs env (applied name' cph) {})
  check "disjoint: a new name, and an expression with that name: violated"
    (!checkDisjs env (applied name' (Exp.mkApp 2 (Ty.mk 0 false) #[name', cph])) {})
  -- leftover names
  let n (k : Nat) : Exp := Exp.ofVar (Node.var (freshBase + k) (Ty.mk 1 true))
  let wal (x p : Exp) : Exp := Exp.mkApp 2 (Ty.mk 0 false) #[x, p]
  let alcomi := id "alcomi"
  -- two steps of alcomi {x y} (ph: wff x y): each needs its two names different
  let tree := ProofTree.step (id "ax_mp") #[cph, cph]
    #[.step alcomi #[n 0, n 1, cph] #[.hyp 0], .step alcomi #[n 2, n 3, wal (n 2) cph] #[.hyp 0]]
  checkEq "names: the pairs that must differ" ((nameConflicts db tree).map fun (a, b) => (Node.varId a - freshBase, Node.varId b - freshBase))
    #[(0, 1), (2, 3)]
  checkEq "names: merged where the steps allow it"
    ((mergeNames db tree).vars.map fun v => Node.varId v - freshBase) #[0, 1]

/-- The replay test on the first theorems of the set.mm translation, if the corpus is
built: every proof is reconstructed, and the file with the new bodies is valid. The
whole file is `mm0-whitehead prove replay .tools/corpus/setmm.mmb`. -/
def replayCorpusTests : TestM Unit := do
  let path : System.FilePath := ".tools/corpus/setmm.mmb"
  if !(← path.pathExists) then
    skip "replay of the set.mm translation" "run scripts/build-corpus.sh"
    return
  let file ←
    match MmbFile.parse (← IO.FS.readBinFile path) with
    | .ok f => pure f
    | .error e => check "replay corpus: the file is read" false e.msg; return
  let db ←
    match Db.ofFile file with
    | .ok db => pure db
    | .error msg => check "replay corpus: the file becomes a database" false msg; return
  let (stats, bodies) ← replay db { last := 6000 } fun _ => pure ()
  check s!"replay corpus: the first {stats.theorems} theorems of set.mm are reconstructed"
    (stats.failed == 0 && stats.replayed == stats.theorems && stats.theorems > 5000)
    s!"{stats.replayed} of {stats.theorems}"
  checkEq "replay corpus: step for step" stats.stepsOut stats.stepsIn
  match MmbFile.parse (file.withBodies bodies) with
  | .error e => check "replay corpus: the file with the new bodies is read" false e.msg
  | .ok f2 =>
    match Whitehead.Verify.checkProofs f2 with
    | .ok () => check "replay corpus: the file with the new bodies is valid" true
    | .error e => check "replay corpus: the file with the new bodies is valid" false (e.format f2 "replayed")
  IO.println s!"replay corpus: {stats.replayed} proofs of set.mm reconstructed, {stats.stepsOut} steps"

end Tests.Prove
