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
  | .conv t path unfold child =>
    s!"({if unfold then "unfold" else "fold"} {db.terms[t]!.name}@{path} {skeletonText db child})"

partial def proofText (db : Db) : ProofTree → String
  | .hyp i => s!"h{i}"
  | .step t _ children =>
    if children.isEmpty then db.asserts[t]!.name
    else s!"({db.asserts[t]!.name} {" ".intercalate (children.map (proofText db)).toList})"
  | .conv t path unfold _ _ child =>
    s!"({if unfold then "unfold" else "fold"} {db.terms[t]!.name}@{path} {proofText db child})"

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
      | .ok none => "shared conversion"
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
  check "search: a proof whose condition on a bound variable fails late stops there, not at the verifier"
    (alrimi.rejected == 0 && alrimi.env.counters.disjoint > 0)
    s!"{alrimi.rejected} rejected, {alrimi.env.counters.disjoint} stopped"
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
  -- a goal with a variable to be found: something of the shape `?q -> ps`. Constants 0
  -- and 1 are ph and ps; the variable is the first fresh one.
  let wffTy := Ty.mk 0 false
  let c (k : Nat) : Exp := ⟨#[Node.const k wffTy]⟩
  let q : Exp := Exp.ofVar (Node.var freshBase wffTy)
  let wi (a b : Exp) : Exp := Exp.mkApp 0 wffTy #[a, b]
  let answerTask : Task :=
    { limit := id "syl" + 1, sorts := 1, terms := 2,
      consts := #[{ ty := wffTy, names := #[] }, { ty := wffTy, names := #[] }],
      premises := #[c 0], goal := wi q (c 1), metas := #[q.nodes[0]!] }
  let answerEnv := Env.init db index answerTask
  let answered ← searchWith acceptAny answerEnv breadthFirst { maxProps := 5000 }
  checkEq "answer: a goal with a variable is proved, and the variable found"
    ((answered.answer.map (db.showExp · #["ph", "ps"])).getD "none") "(wi ps ps)"
  checkEq "answer: the first proof, breadth first, is the shortest way to such a goal"
    ((answered.proof.map (proofText db)).getD "none") "id"
  -- without `id` and what follows it, the premise is needed: from ph, by ax_3,
  -- (~ps -> ~ph) -> ps
  let earlier ← searchWith acceptAny { answerEnv with task := { answerTask with limit := id "id" } }
    breadthFirst { maxProps := 5000 }
  checkEq "answer: another answer when less may be used"
    ((earlier.answer.map (db.showExp · #["ph", "ps"])).getD "none", (earlier.proof.map (proofText db)).getD "none")
    ("(wi (wi (wn ps) (wn ph)) ps)", "(mpd (a1i h0) ax_3)")
  checkEq "answer: the value of the metavariable" (earlier.values.map (db.showExp · #["ph", "ps"]))
    #["(wi (wn ps) (wn ph))"]
  -- with ph -> ps as a second premise the goal unifies with it, and that is the proof
  let byPremise ← searchWith acceptAny
    (Env.init db index { answerTask with premises := #[c 0, wi (c 0) (c 1)] }) breadthFirst { maxProps := 5000 }
  checkEq "answer: a goal that unifies with a premise is proved by it"
    ((byPremise.answer.map (db.showExp · #["ph", "ps"])).getD "none", (byPremise.proof.map (proofText db)).getD "none",
      byPremise.values.map (db.showExp · #["ph", "ps"]))
    ("(wi ph ps)", "h1", #["ph"])
  -- the marking of the variables of a theorem: free variables, which become constants,
  -- or metavariables. a1i (ph ps: wff) (h: ph): ps -> ph, with ph to be found
  let marked := db.task (id "a1i") #[0]
  checkEq "metavariables: a marked binder is a variable of the tree, the others are constants"
    (db.showExp marked.goal #["ph", "ps"], marked.premises.map (db.showExp · #["ph", "ps"]), marked.metas.size)
    ("(wi ps ?0)", #["?0"], 1)
  checkEq "metavariables: without marks the task is as before" (db.task (id "a1i") #[]).metas.size 0
  check "metavariables: a bound binder cannot be marked"
    ((db.metasFault (id "alimi") #[0]).isSome && (db.metasFault (id "alimi") #[1]).isNone)
  check "metavariables: nor a binder that is not there" (db.metasFault (id "a1i") #[2]).isSome
  checkEq "metavariables: a mark that cannot be followed is not" (db.task (id "alimi") #[0]).metas.size 0
  let markedFound ← searchWith acceptAny (Env.init db index marked) breadthFirst { maxProps := 5000 }
  checkEq "metavariables: the prover finds a value, and reports the goal as it is proved"
    ((markedFound.proof.map (proofText db)).getD "none", (markedFound.answer.map (db.showExp · #["ph", "ps"])).getD "none",
      markedFound.values.map (db.showExp · #["ph", "ps"]))
    ("ax_1", "(wi ps (wi ?1 ps))", #["(wi ?1 ps)"])
  -- mpd (ph ps ch) (h1: ph -> ps) (h2: ph -> ps -> ch): ph -> ch, with ch to be found:
  -- the goal unifies with the first premise, and not with the second (ch would contain
  -- itself)
  let direct ← searchWith acceptAny (Env.init db index (db.task (id "mpd") #[2])) breadthFirst { maxProps := 5000 }
  checkEq "metavariables: a goal that unifies with a premise is proved by it"
    ((direct.proof.map (proofText db)).getD "none", direct.values.map (db.showExp · #["ph", "ps", "ch"]))
    ("h0", #["ps"])
  -- all variants: D from A, B, A -> C, B -> C and C -> D by modus ponens twice. C has
  -- two proofs, which give the node above the same instance and differ below it; both
  -- must reach the root (`ruProofSubKey` is of the whole substitution). Every proof is
  -- refused here, so that the search goes on and the root collects them.
  let variantsTask : Task :=
    { limit := id "a1i", sorts := 1, terms := 2,
      consts := (Array.range 4).map fun _ => { ty := wffTy, names := #[] },
      premises := #[c 0, c 1, wi (c 0) (c 2), wi (c 1) (c 2), wi (c 2) (c 3)], goal := c 3 }
  let variants ← searchWith (fun _ _ _ => .error "every proof is asked for") (Env.init db index variantsTask)
    breadthFirst { maxProps := 60 }
  let rootProofs := variants.env.hyps[0]!.proofs.map fun p => proofText db (makeProofTree variants.env p)
  -- the two proofs of C give the node above the same substitution and no open
  -- conditions, so one of them is kept (`proofKey`, decided 2026-10-11)
  check "variants: of two proofs that differ only below a node, one is kept"
    (rootProofs.size == 1 && (rootProofs.contains "(ax_mp (ax_mp h0 h2) h4)" || rootProofs.contains "(ax_mp (ax_mp h1 h3) h4)"))
    s!"{rootProofs}"
  -- and two proofs with the same substitution: B -> (A -> A) by a1i from A -> A, which
  -- `id` proves and `dummy` proves, neither binding a variable of the tree. Nothing
  -- shows that one can stand for the other, so both are kept.
  let sameTask : Task :=
    { limit := db.asserts.size, sorts := 2, terms := 3,
      consts := (Array.range 2).map fun _ => { ty := wffTy, names := #[] },
      premises := #[], goal := wi (c 1) (wi (c 0) (c 0)) }
  let same ← searchWith (fun _ _ _ => .error "every proof is asked for") (Env.init db index sameTask)
    breadthFirst { maxProps := 5000 }
  let sameProofs := same.env.hyps[0]!.proofs.map fun p => proofText db (makeProofTree same.env p)
  check "variants: of two proofs with the same substitution, one is kept"
    (sameProofs.contains "(a1i id)" != sameProofs.contains "(a1i dummy)") s!"{sameProofs.extract 0 12}"
  check "variants: and no proof is there twice"
    (sameProofs.size == (sameProofs.foldl (init := ({} : Std.HashSet String)) (·.insert ·)).size)
    s!"{sameProofs.size} proofs"
  -- the forward direction: from the premises and the assertions without hypotheses
  let hypIndexes := db.hypIndexes
  let forwardEnv (name : String) : Env := Env.init db index (db.task (id name)) hypIndexes
  let a1iForward ← search vc (forwardEnv "a1i") forwardOnly limits
  checkEq "forward: a1i from its premise and ax_1, by ax_mp"
    ((a1iForward.proof.map (proofText db)).getD "none") "(ax_mp h0 ax_1)"
  check "forward: the proof came from a fact that is the goal"
    (a1iForward.env.counters.facts > 0 && a1iForward.env.counters.joins == 1)
  let con1Forward ← search vc (forwardEnv "con1") forwardOnly limits
  check "forward: a front that reaches its limit of facts ends the search"
    (con1Forward.ending == .exhausted && con1Forward.proof.isNone &&
      (con1Forward.env.forward.map (·.count)) == some limits.maxFacts)
  let mpcomBoth ← search vc (forwardEnv "mpcom") bidirectional limits
  checkEq "both directions: mpcom" ((mpcomBoth.proof.map (proofText db)).getD "none") "(com12 id)"
  let (bothRows, bothBodies) ← searchAll db { strategy := "both", limits := { maxProps := 3000, maxMs := 20000 } }
    fun _ => pure ()
  let bothProved := (bothRows.filter (·.ending == .proved)).size
  check "both directions: most of the fixture is proved" (bothProved ≥ 13) s!"{bothProved} of {bothRows.size}"
  check "both directions: no proof is rejected by the verifier" (bothRows.all (·.rejected == 0))
  match MmbFile.parse (file.withBodies bothBodies) with
  | .error e => check "both directions: the file with the proofs found is read" false e.msg
  | .ok f2 =>
    match Whitehead.Verify.checkProofs f2 with
    | .ok () => check "both directions: the file with the proofs found is valid" true
    | .error e => check "both directions: the file with the proofs found is valid" false (e.format f2 "both")
  -- all variants in the forward front: B from A and A -> B, and from C and C -> B, is two
  -- facts, and D follows from each
  let fwdTask : Task :=
    { limit := id "a1i", sorts := 1, terms := 2,
      consts := (Array.range 4).map fun _ => { ty := wffTy, names := #[] },
      premises := #[c 0, wi (c 0) (c 1), c 2, wi (c 2) (c 1), wi (c 1) (c 3)], goal := c 3 }
  let fwdVariants ← searchWith (fun _ _ _ => .error "every proof is asked for")
    (Env.init db index fwdTask hypIndexes) forwardOnly { maxProps := 5000, maxFacts := 64 }
  let factsOf (env : Env) (e : Exp) : Array String :=
    env.hyps.filterMap fun h => if h.expr == e then h.factProof.map (proofText db) else none
  let bs := factsOf fwdVariants.env (c 1)
  check "forward: a statement derived by two applications is two facts"
    (bs.contains "(ax_mp h0 h1)" && bs.contains "(ax_mp h2 h3)") s!"{bs}"
  let ds := factsOf fwdVariants.env (c 3)
  check "forward: what follows from it is derived; of one application's proofs with the same key, one is kept"
    (ds.contains "(ax_mp (ax_mp h0 h1) h4)" || ds.contains "(ax_mp (ax_mp h2 h3) h4)") s!"{ds}"
  -- but one application of an assertion to the same facts is made once: no two facts
  -- have the same proof
  let factProofs (env : Env) : Array String := env.hyps.filterMap fun h => h.factProof.map (proofText db)
  let distinct (texts : Array String) : Bool :=
    texts.size == (texts.foldl (init := ({} : Std.HashSet String)) (·.insert ·)).size
  check "forward: no proof is made twice" (distinct (factProofs con1Forward.env) && distinct (factProofs fwdVariants.env))
    s!"{(factProofs con1Forward.env).size} and {(factProofs fwdVariants.env).size} facts"
  -- each use of a fact has its own variables
  let seeded := (← (seedForward 100).run (forwardEnv "id")).2
  let schematic := (seeded.forward.map (·.front)).getD #[] |>.filter fun f => seeded.hyps[f]!.expr.hasVars
  check "forward: the axioms without hypotheses are seeded as facts with variables" (schematic.size ≥ 3)
  let ((copy1, _, _), afterOne) ← (freshCopy schematic[0]!).run seeded
  let ((copy2, _, _), _) ← (freshCopy schematic[0]!).run afterOne
  check "forward: two uses of a fact share no variable"
    (copy1.vars.all fun x => !copy2.vars.contains x)
  -- the condition on bound variables, on an application of ax_5 in the task of alimi,
  -- whose constants are x, ph and ps, the last two depending on x
  let env := Env.init db index task
  let ax5 := db.asserts[id "ax_5"]!
  let cx : Exp := ⟨#[Node.const 0 task.consts[0]!.ty]⟩
  let cph : Exp := ⟨#[Node.const 1 task.consts[1]!.ty]⟩
  let mvar : Exp := Exp.ofVar (Node.var freshBase (Ty.mk 0 false))
  let name' : Exp := Exp.ofVar (Node.var (freshBase + 1) (Ty.mk 1 true))
  let applied (x ph : Exp) : PropNode :=
    { step := .assertion ax5.id, rule := ax5, parent := 0, sub := {},
      outer := { map := (({} : Std.HashMap Nat SubExp).insert 0 (SubExp.mk' ax5.vars[0]! x)).insert 1
                  (SubExp.mk' ax5.vars[1]! ph) } }
  -- the outcome as text: violated, or the number of conditions left open
  let conds (prop : PropNode) (theta : Subst) (visible : List Nat := []) : String :=
    match openConds env prop theta (Std.HashSet.ofList visible) #[] with
    | none => "violated"
    | some cs => s!"{cs.size} open"
  checkEq "disjoint: x given for x, and ph, which depends on x" (conds (applied cx cph) {}) "violated"
  checkEq "disjoint: x, and a variable that may still become anything"
    (conds (applied cx mvar) {}) "1 open"
  checkEq "disjoint: the same, once the variable is ph"
    (conds (applied cx mvar) (Subst.single mvar.nodes[0]! cph)) "violated"
  -- in the task of alrimi the constant 1 is ph, which does not depend on x
  let envR := Env.init db index (db.task (id "alrimi"))
  let closedPh : Exp := ⟨#[Node.const 1 (Ty.mk 0 false)]⟩
  checkEq "disjoint: x, and a variable that has become an expression without x: settled"
    (match openConds envR (applied cx mvar) (Subst.single mvar.nodes[0]! closedPh) {} #[] with
      | none => "violated"
      | some cs => s!"{cs.size} open") "0 open"
  checkEq "disjoint: a new name that nothing above can replace, and ph: settled, it becomes a dummy"
    (conds (applied name' cph) {}) "0 open"
  checkEq "disjoint: a new name that a node above can still replace, and ph"
    (conds (applied name' cph) {} [freshBase + 1]) "1 open"
  checkEq "disjoint: a new name, and an expression with that name"
    (conds (applied name' (Exp.mkApp 2 (Ty.mk 0 false) #[name', cph])) {}) "violated"
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
