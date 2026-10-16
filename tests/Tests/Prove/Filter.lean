/-
Tests of patterns, filters and the language of tactics and filters
(`Prove/Pattern.lean`, `Prove/Filter.lean`, `Prove/Combinators.lean`, `Prove/Dsl.lean`)
on `tests/fixtures/prove/logic.mmb`, with the notations of `logic.mm0`: patterns read
in the notation, with holes, and their errors; filters over the variants of a goal node
and over deductions; a sample that a seed fixes; strategies restricted by a filter, by
a size and by a depth, and in sequence; and the reading of the language, with its errors.
-/
import Whitehead.Prove.Session
import Whitehead.Prove.Measure
import Tests.Prove.Engine

open Whitehead.Mmb Whitehead.Prove

namespace Tests.Prove

def logicSpecPath : System.FilePath := "tests/fixtures/prove/logic.mm0"

def filterTests : TestM Unit := do
  let bytes ← IO.FS.readBinFile logicPath
  let some file := MmbFile.parse bytes |>.toOption
    | check "filters: the fixture is read" false; return
  let some db := Db.ofFile file |>.toOption
    | check "filters: the fixture becomes a database" false; return
  let st ← match ← Whitehead.Mm0.load logicSpecPath with
    | .error e => check "filters: the specification is read" false e.format; return
    | .ok spec =>
      match Whitehead.Mm0.elaborateState spec with
      | .ok st => pure st
      | .error e => check "filters: the specification is read" false e.format; return
  let spec := Notation.ofSpec st file
  let vc := Whitehead.Verify.Ctx.ofFile file
  let id := thmId db
  checkEq "notation: the terms of the specification in the proof file" spec.terms #[0, 1, 2]
  checkEq "notation: a theorem of the specification in the proof file" (spec.specThm (id "syl")).isSome true
  let startOn (name : String) : IO Session := Session.startFor vc (Env.init db db.index (db.task (id name)))
  -- patterns, for a1i: ph ps are the constants 0 1, its goal ps -> ph
  let a1i ← startOn "a1i"
  let ctx := a1i.dslCtx (some spec)
  let pat (text : String) : Except String Exp :=
    (spec.pattern (id "a1i") ctx.vars text).mapError fun e => s!"{e.pos}: {e.msg}"
  let goal := a1i.env.task.goal
  let matchesGoal (text : String) : Bool :=
    match pat text with
    | .ok p => goal.matchesPattern p
    | .error _ => false
  check "pattern: the goal matches itself" (matchesGoal "ps -> ph")
  check "pattern: a hole matches anything" (matchesGoal "_" && matchesGoal "ps -> _" && matchesGoal "_ -> ph")
  check "pattern: a variable of the theorem matches only itself" (!matchesGoal "ph -> _" && !matchesGoal "_ -> ps")
  check "pattern: the shape must agree" (!matchesGoal "_ -> _ -> _" && !matchesGoal "~ _")
  check "pattern: a hole in a bound position"
    ((spec.pattern (id "alimi") ctx.vars "A. _ _ -> _").isOk)
  match pat "ps ->" with
  | .ok _ => check "pattern: an unfinished formula is refused" false
  | .error msg => check "pattern: an unfinished formula is refused" (contains msg "the formula ends here") msg
  match pat "ps -> foo" with
  | .ok _ => check "pattern: an unknown name is refused" false
  | .error msg => check "pattern: an unknown name is refused" (contains msg "unknown variable or term `foo`") msg
  -- filters over the variants of mpd's root, ph -> ch
  let mpd ← startOn "mpd"
  let ctx := mpd.dslCtx (some spec)
  let sel (text : String) : Except String (Nat × Array Variant) := do
    let f ← (Dsl.parseFilter ctx text).mapError fun e => Dsl.ParseError.show text e
    mpd.select 0 f 3
  let count (text : String) : Nat := match sel text with | .ok (n, _) => n | .error _ => 1000000
  let all := mpd.env.hyps[0]!.children.size
  checkEq "filter: all" (count "all") all
  checkEq "filter: by name" (count "name(ax_mp)") 1
  checkEq "filter: by name, with *" (count "name(a*)") (count "or(name(a1i), name(a2i), name(ax_mp))")
  checkEq "filter: not" (count "not(name(ax_mp))") (all - 1)
  checkEq "filter: the kind" (count "kind(assertion)") all
  checkEq "filter: the result is the goal" (count "result($ ph -> ch $)") all
  checkEq "filter: a result that is not the goal" (count "result($ ch -> _ $)") 0
  checkEq "filter: the premises" (count "and(name(ax_mp), premises(2))") 1
  checkEq "filter: a new goal by a pattern" (count "and(name(ax_mp), goal($ _ -> ph -> ch $))") 1
  checkEq "filter: a new goal that is not there" (count "and(name(ax_mp), goal($ ch -> _ $))") 0
  checkEq "filter: scope" (count "scope(ax_mp, a1i)") (count "or(name(ax_mp), name(a1i))")
  checkEq "filter: a new goal that is a bare variable" (count "and(name(ax_mp), bare)") 1
  -- ax_mp's minor premise ?ph fits every premise, but a bare variable does not count
  checkEq "filter: a bare new goal is not one that a premise proves" (count "and(name(ax_mp), hyp)") 0
  checkEq "filter: neither" (count "and(name(a1i), or(bare, hyp))") 0
  -- ax_mp's major premise ?ph -> ph -> ch: as a pattern it is not ph -> ph -> ch, but could become it
  checkEq "filter: goal matches exactly" (count "and(name(ax_mp), goal($ ph -> ph -> ch $))") 0
  checkEq "filter: fits lets a metavariable become anything" (count "and(name(ax_mp), fits($ ph -> ph -> ch $))") 1
  checkEq "filter: what a step proves" (count "proves($ ph -> ch $)") all
  checkEq "filter: the goal has no variable" (count "ground") all
  -- syl: mpd's new goal ph -> ?ps is proved by the premise ph -> ps
  let syl ← startOn "syl"
  match Dsl.parseFilter (syl.dslCtx (some spec)) "and(name(mpd), hyp)", syl.select 0 .all 0 with
  | .ok f, .ok _ =>
    checkEq "filter: a new goal that a premise proves" ((syl.select 0 f 1).toOption.map (·.1)) (some 1)
  | _, _ => check "filter: hyp on syl" false
  match sel "name(ax_mp)" with
  | .ok (_, vs) => checkEq "filter: the sample is the variant" (vs.map (·.name)) #["ax_mp"]
  | .error msg => check "filter: the sample is the variant" false msg
  -- a sample: n of them, the same for the same seed, in the order of the variants
  let some f := (Dsl.parseFilter ctx "all").toOption | return
  match mpd.select 0 f 2 7, mpd.select 0 f 2 7, mpd.select 0 f 100 7 with
  | .ok (_, a), .ok (_, b), .ok (_, c) =>
    check "sample: n of them, the same for the same seed, in order"
      (a.size == min 2 all && (a.map (·.prop)) == (b.map (·.prop)) && c.size == all &&
        (a.map (·.prop)) == (a.map (·.prop)).qsort (· < ·))
  | _, _, _ => check "sample: n of them, the same for the same seed, in order" false
  -- tactics restricted by filters
  let limits : Limits := { maxProps := 5000, maxMs := 20000 }
  let runOn (name text : String) : IO (Except String (Session × Ending)) := do
    let s ← startOn name
    match Dsl.parseTactic (s.dslCtx (some spec)) text with
    | .error e => return .error (Dsl.ParseError.show text e)
    | .ok t =>
      match ← s.run t.strategy limits with
      | .ok (s, ending, _) => return .ok (s, ending)
      | .error msg => return .error msg
  let foundText (s : Session) : String := (s.found.map (proofText db ·.proof)).getD "none"
  match ← runOn "a1i" "filter(scope(ax_mp, ax_1), bfs)" with
  | .ok (s, ending) =>
    check "tactic: bfs within a scope proves a1i" (ending == .proved && foundText s == "(ax_mp h0 ax_1)") (foundText s)
  | .error msg => check "tactic: bfs within a scope proves a1i" false msg
  match ← runOn "a1i" "filter(scope(ax_1), bfs)" with
  | .ok (s, ending) =>
    check "tactic: a scope that admits no variant ends at once, nothing expanded"
      (ending == .exhausted && s.env.counters.expanded == 0)
  | .error msg => check "tactic: a scope that admits no variant ends at once" false msg
  match ← runOn "con1" "limited(bfs, size=50)" with
  | .ok (s, ending) =>
    check "tactic: limited by size stops after its nodes"
      (ending == .exhausted && s.found.isNone && s.env.props.size ≥ 50 && s.env.props.size < 5000)
      s!"{s.env.props.size} nodes"
  | .error msg => check "tactic: limited by size" false msg
  match ← runOn "syl" "limited(bfs, depth=1)" with
  | .ok (s, ending) =>
    check "tactic: at depth 1, only the variants of the root" (ending == .exhausted && s.found.isNone &&
      (Array.range s.env.props.size).all fun p => !s.env.props[p]!.expanded || s.env.propDepth p == 1)
  | .error msg => check "tactic: limited by depth" false msg
  match ← runOn "syl" "limited(bfs, depth=3)" with
  | .ok (s, ending) => check "tactic: at depth 3, syl is proved" (ending == .proved) (foundText s)
  | .error msg => check "tactic: at depth 3, syl is proved" false msg
  match ← runOn "syl" "seq(limited(bfs, size=10), done, bfs)" with
  | .ok (s, ending) =>
    check "tactic: seq goes on to the next" (ending == .proved && foundText s == "(mpd h1 (a1i h0))") (foundText s)
  | .error msg => check "tactic: seq" false msg
  -- filters over deductions: ph -> ps, ps -> ch, ps -> th, as in the forward session test
  let wffTy := Ty.mk 0 false
  let c (k : Nat) : Exp := ⟨#[Node.const k wffTy]⟩
  let wi (a b : Exp) : Exp := Exp.mkApp 0 wffTy #[a, b]
  let task : Task :=
    { limit := id "a2d", sorts := 1, terms := 2,
      consts := (Array.range 4).map fun _ => { ty := wffTy, names := #[] },
      premises := #[wi (c 0) (c 1), wi (c 1) (c 2), wi (c 1) (c 3)], goal := wi (c 3) (c 3) }
  let s ← Session.start acceptAny (Env.init db db.index task db.hypIndexes) (forward := true) { maxFacts := 64 }
  let ctx := s.dslCtx (some spec)
  -- the premises; the front also has the axioms without hypotheses, with variables
  let premises := s.front.filter fun f => task.premises.contains s.env.hyps[f]!.expr
  match ← s.deduce premises with
  | .error msg => check "filter: deductions" false msg
  | .ok (s, made) =>
    let selF (text : String) : Nat :=
      match Dsl.parseFilter ctx text with
      | .ok f => (s.selectFacts made f 10).1
      | .error _ => 1000000
    checkEq "filter: deductions by the fact deduced" (selF "result($ ph -> _ $)") 2
    checkEq "filter: deductions by name" (selF "and(name(syl), result($ ph -> th $))") 1
    checkEq "filter: a premise is not a deduction" (s.selectFacts s.front .all 10).1
      ((s.front.filter fun f => (s.env.factView? f).isSome).size)

/-- The variants of the goal nodes on a known proof's path (`Prove/Measure.lean`). -/
def measureTests : TestM Unit := do
  let bytes ← IO.FS.readBinFile logicPath
  let some file := MmbFile.parse bytes |>.toOption | check "measure: the fixture is read" false; return
  let some db := Db.ofFile file |>.toOption | check "measure: the fixture becomes a database" false; return
  let some i := (Array.range file.stmts.size).find? fun i =>
      (match file.stmts[i]!.kind with | .thm _ => true | _ => false) &&
        file.stmts[i]!.index == thmId db "mpd"
    | check "measure: mpd is in the file" false; return
  match ← variantCounts db db.index { maxProps := 5000 } i with
  | some (counts, limited) =>
    -- (ax_mp h0 (ax_mp h1 ax_2)): three steps, so three nodes with a choice
    check "measure: a count for each step of the known proof, each at least one"
      (counts.size == 3 && counts.all (· ≥ 1) && !limited) s!"{counts}"
    check "measure: the summary counts the nodes" (contains (variantSummary counts) "3 nodes") (variantSummary counts)
  | none => check "measure: mpd's proof is measured" false
  -- the shape of an expression: terms and constants to a depth, holes below and for variables
  let wffTy := Ty.mk 0 false
  let c (k : Nat) : Exp := ⟨#[Node.const k wffTy]⟩
  let wi (a b : Exp) : Exp := Exp.mkApp 0 wffTy #[a, b]
  let hole : Exp := ⟨#[holeNode]⟩
  let v : Exp := Exp.ofVar (Node.var freshBase wffTy)
  let e := wi (wi (c 0) v) (c 1)
  check "measure: shapes to depths 0 to 3"
    (e.shape 0 == hole && e.shape 1 == wi hole hole && e.shape 2 == wi (wi hole hole) (c 1) &&
      e.shape 3 == wi (wi (c 0) hole) (c 1))
  -- every node of every proof of the fixture: the described variant passes, and fewer remain
  let mut all := #[]
  for j in [0:file.stmts.size] do
    if let .thm _ := file.stmts[j]!.kind then
      if let some (cs, _) ← nodeCounts db db.index { maxProps := 5000 } #[1, 2, 3] j then all := all ++ cs
  check "measure: described, the known variant passes, and no more remain than there are"
    (!all.isEmpty && all.all fun n => n.kept && n.shaped.all (· ≤ n.variants) && n.shaped.all (· ≥ 1))
    s!"{all.size} nodes"

/-- The uses of the assertions in the proofs before a theorem, the `used` atom, and the
order of a selection by them (`Prove/Uses.lean`). -/
def usesTests : TestM Unit := do
  let bytes ← IO.FS.readBinFile logicPath
  let some file := MmbFile.parse bytes |>.toOption | check "uses: the fixture is read" false; return
  let some db := Db.ofFile file |>.toOption | check "uses: the fixture becomes a database" false; return
  let id := thmId db
  let uses := Uses.ofFile file db.asserts.size
  -- ax_mp: in a1i, a2i, mpd; ax_2: in a2i, mpd; ax_1: in a1i, id, com12
  checkEq "uses: none before the first proof" (uses.before (id "ax_mp") (id "a1i")) 0
  checkEq "uses: a theorem's own proof does not count" (uses.before (id "ax_mp") (id "a2i")) 1
  checkEq "uses: the proofs before, each once" (uses.before (id "ax_mp") (id "id")) 3
  checkEq "uses: of a theorem" (uses.before (id "a1i") (id "a2d")) 1
  checkEq "uses: an axiom that one proof uses, the last" (uses.before (id "sp") 1000) 1
  -- in a session on syl: the variants of its root, by uses
  let vc := Whitehead.Verify.Ctx.ofFile file
  let s ← Session.startFor vc { Env.init db db.index (db.task (id "syl")) with uses }
  match s.select 0 .all 100 0 true, s.select 0 (.used 2) 100 with
  | .ok (n, ordered), .ok (k, used) =>
    let u (v : Variant) : Nat := s.env.stepUses v.step
    check "uses: ordered, the most used first" (ordered.size == n &&
      (Array.range (n - 1)).all fun j => u ordered[j]! ≥ u ordered[j + 1]!)
      s!"{ordered.map fun v => (v.name, u v)}"
    check "uses: used(2) keeps those used in two proofs or more"
      (k == (ordered.filter (u · ≥ 2)).size && used.all (u · ≥ 2)) s!"{k}"
  | _, _ => check "uses: a selection on syl" false

def dslTests : TestM Unit := do
  let bytes ← IO.FS.readBinFile logicPath
  let some db := (MmbFile.parse bytes |>.toOption).bind (Db.ofFile · |>.toOption)
    | check "dsl: the fixture becomes a database" false; return
  let ctx : Dsl.Ctx := { db }
  let tacticError (text : String) : String :=
    match Dsl.parseTactic ctx text with
    | .ok _ => "accepted"
    | .error e => s!"{e.pos}: {e.msg}"
  let filterError (text : String) : String :=
    match Dsl.parseFilter ctx text with
    | .ok _ => "accepted"
    | .error e => s!"{e.pos}: {e.msg}"
  match Dsl.parse "limited(bfs, size=4096, depth = 5)" with
  | .ok (.call "limited" 0 args) =>
    check "dsl: a term with named arguments" (args.size == 3 && args[1]!.1 == some "size" && args[2]!.1 == some "depth")
  | _ => check "dsl: a term with named arguments" false
  checkEq "dsl: tactics" (#["bfs", "forward", "both", "done", "filter(name(ax_*), bfs)",
      "limited(bfs, 100, 3)", "seq(bfs, limited(filter(not(kind(unfold)), bfs), depth=2))",
      "filter(and(premises(max=1), scope(ax_mp, a1i)), bfs)", "filter(used(min=3), bfs)",
      "focus(0, filter(not(bare), bfs))"].map tacticError)
    #["accepted", "accepted", "accepted", "accepted", "accepted", "accepted", "accepted", "accepted", "accepted",
      "accepted"]
  checkEq "dsl: focus needs a node" (tacticError "focus(bfs)") "6: `node` of `focus` is a number"
  checkEq "dsl: unclosed arguments" (tacticError "limited(bfs") "11: the arguments of `limited` are not closed by `)`"
  checkEq "dsl: text after the term" (tacticError "bfs)") "3: expected the end of the text"
  checkEq "dsl: a missing argument" (tacticError "filter(all)") "0: `filter` needs a tactic"
  checkEq "dsl: a tactic where a filter is expected" (tacticError "filter(bfs, bfs)")
    "7: `bfs` is a tactic; a filter is expected here"
  checkEq "dsl: a filter where a tactic is expected" (tacticError "seq(bfs, all)") "9: `all` is a filter; a tactic is expected here"
  checkEq "dsl: an unknown tactic" (tacticError "dfs") "0: unknown tactic `dfs`"
  checkEq "dsl: an unknown parameter" (tacticError "limited(bfs, sise=3)") "18: `limited` has no parameter `sise`"
  checkEq "dsl: a number where a tactic is expected" (tacticError "seq(3)") "4: a tactic is expected here, not a number"
  checkEq "dsl: an unexpected character" (tacticError "bfs;") "3: unexpected character `;`"
  checkEq "dsl: a kind that is not one" (filterError "kind(other)") "0: `kind` is assertion, unfold or fold, not `other`"
  checkEq "dsl: an assertion that is not there" (filterError "scope(ax_mp, nosuch)") "13: no assertion is named `nosuch`"
  checkEq "dsl: a pattern without a specification" (filterError "goal($ _ $)")
    "5: a pattern needs the specification (.mm0) for its notation"
  checkEq "dsl: an unclosed formula" (filterError "goal($ _ ") "5: this formula has no closing `$`"
  check "dsl: help lists every component" (Dsl.docs.all fun d => contains Dsl.help d.signature)

end Tests.Prove
