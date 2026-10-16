/-
Tests of intermediate goals (`Forward.lean`, "Intermediate goals"; `Session.goal`) on
`tests/fixtures/prove/logic.mmb`, with the notations of `logic.mm0`: an intermediate
goal proved backward by a choice, and then used in the proof of the main goal, offered
before or after the choice that needs it; one with a hole, a metavariable that its
proof finds; one reached by a fact of the forward front; two in a chain, the second
using the first; the guard that keeps the fact of an intermediate goal out of its own
tree; and the errors of reading one.
-/
import Whitehead.Prove.Session
import Tests.Prove.Filter
import Tests.Prove.Session

open Whitehead.Mmb Whitehead.Prove

namespace Tests.Prove

def hintTests : TestM Unit := do
  let bytes ← IO.FS.readBinFile logicPath
  let some file := MmbFile.parse bytes |>.toOption | check "hints: the fixture is read" false; return
  let some db := Db.ofFile file |>.toOption | check "hints: the fixture becomes a database" false; return
  let st ← match ← Whitehead.Mm0.load logicSpecPath with
    | .error e => check "hints: the specification is read" false e.format; return
    | .ok spec =>
      match Whitehead.Mm0.elaborateState spec with
      | .ok st => pure st
      | .error e => check "hints: the specification is read" false e.format; return
  let spec := Notation.ofSpec st file
  let vc := Whitehead.Verify.Ctx.ofFile file
  let id := thmId db
  let startOn (name : String) : IO Session := Session.startFor vc (Env.init db db.index (db.task (id name)))
  let foundText (s : Session) : String := (s.found.map (proofText db ·.proof)).getD "none"
  let goalOf (s : Session) (text : String) : TestM (Option (Session × Nat)) := do
    match ← s.goalText spec text with
    | .ok r => return some r
    | .error msg => check s!"hints: the intermediate goal {text}" false msg; return none
  let chooseAt (s : Session) (h : Nat) (name : String) : TestM (Option Session) := do
    match variantNamed s h name with
    | none => check s!"hints: {name} is a variant of node {h}" false; return none
    | some v =>
      match ← s.choose h #[v.prop] with
      | .ok s => return some s
      | .error msg => check s!"hints: {name} is chosen at node {h}" false msg; return none
  -- mpd: ph -> ps, ph -> ps -> ch |- ph -> ch, with the intermediate goal (ph -> ps) -> ph -> ch
  let s ← startOn "mpd"
  let some (s, h) ← goalOf s "(ph -> ps) -> ph -> ch" | return
  check "hints: the intermediate goal is a goal node, open, with variants, and the session has a front"
    (s.hints == #[h] && s.isGoal h && s.openGoals.contains h && s.env.forward.isSome &&
      (match s.variants h with | .ok vs => !vs.isEmpty | .error _ => false))
  let some s ← chooseAt s h "a2i" | return
  check "hints: proved backward, it is a fact" (!s.openGoals.contains h && s.hintFacts.size == 1)
  checkEq "hints: not yet used" (foundText s) "none"
  let some s ← chooseAt s 0 "ax_mp" | return
  checkEq "hints: used in the proof of the main goal" (foundText s) "(ax_mp h0 (a2i h1))"
  -- the same, the choice at the root first: the subgoals made before are reached too
  let s ← startOn "mpd"
  let some s ← chooseAt s 0 "ax_mp" | return
  check "hints: a session without a front" s.env.forward.isNone
  let some (s, h) ← goalOf s "(ph -> ps) -> ph -> ch" | return
  let some s ← chooseAt s h "a2i" | return
  checkEq "hints: offered after the choice it serves" (foundText s) "(ax_mp h0 (a2i h1))"
  -- a hole: a metavariable, found by the proof of the intermediate goal
  let s ← startOn "mpd"
  let some (s, h) ← goalOf s "_ -> ph -> ch" | return
  check "hints: a hole is a variable of the intermediate goal" s.env.hyps[h]!.expr.hasVars
  let some s ← chooseAt s h "a2i" | return
  check "hints: the fact is the statement with the hole found"
    (s.hintFacts.any fun f => db.showExp s.env.hyps[f]!.expr == "(wi (wi c0 c1) (wi c0 c2))")
    s!"{s.hintFacts.map fun f => db.showExp s.env.hyps[f]!.expr}"
  let some s ← chooseAt s 0 "ax_mp" | return
  checkEq "hints: with a hole, used in the proof of the main goal" (foundText s) "(ax_mp h0 (a2i h1))"
  -- two in a chain: the second, the goal itself, from the first
  let s ← startOn "mpd"
  let some (s, h1) ← goalOf s "(ph -> ps) -> ph -> ch" | return
  let some (s, h2) ← goalOf s "ph -> ch" | return
  let some s ← chooseAt s h1 "a2i" | return
  let some s ← chooseAt s h2 "ax_mp" | return
  check "hints: the second proved from the first, depending on both"
    (s.hintFacts.size == 2 && s.env.hyps[s.hintFacts[1]!]!.deps.qsort (· < ·) == #[0, 1])
    s!"{s.hintFacts.map fun f => s.env.hyps[f]!.deps}"
  checkEq "hints: the main goal from the second" (foundText s) "(ax_mp h0 (a2i h1))"
  -- reached forward: ph -> ps, ps -> ch, ph |- ch, with the intermediate goal ph -> ch
  let wffTy := Ty.mk 0 false
  let c (k : Nat) : Exp := ⟨#[Node.const k wffTy]⟩
  let wi (a b : Exp) : Exp := Exp.mkApp 0 wffTy #[a, b]
  let task : Task :=
    { limit := id "a2d", sorts := 1, terms := 2,
      consts := (Array.range 4).map fun _ => { ty := wffTy, names := #[] },
      premises := #[wi (c 0) (c 1), wi (c 1) (c 2), c 0], goal := c 2 }
  let s ← Session.start acceptAny (Env.init db db.index task db.hypIndexes) (forward := true) { maxFacts := 64 }
  let some (s, h) ← goalOf s "ph -> ch" | return
  check "hints: open before the deduction" (s.openGoals.contains h)
  let premises := s.front.filter fun f => task.premises.contains s.env.hyps[f]!.expr
  match ← s.deduce (premises.extract 0 2) with
  | .error msg => check "hints: reached forward" false msg
  | .ok (s, _) =>
    check "hints: reached by a deduction, it is proved and a fact"
      (!s.openGoals.contains h && !s.hintFacts.isEmpty &&
        s.env.hyps[h]!.proofs.any fun p => match p with | .forward .. => true | _ => false)
  -- the guard: the fact of ph -> ph never proves a subgoal of its own tree
  let s ← startOn "syl"
  let some (s, h) ← goalOf s "ph -> ph" | return
  match Dsl.parseTactic (s.dslCtx (some spec)) "limited(bfs, size=3000)" with
  | .error e => check "hints: the guard" false e.msg
  | .ok t =>
    match ← s.run t.strategy { maxProps := 100000, maxMs := 60000 } with
    | .error msg => check "hints: the guard" false msg
    | .ok (s, _, _) =>
      let proofs := s.env.hyps[h]!.proofs
      check "hints: every proof of the intermediate goal is a fact, and none uses one of them"
        (!proofs.isEmpty && s.hintFacts.size == proofs.size && proofs.all fun p => !(p.hintDeps s.env).contains 0)
        s!"{proofs.size} proofs, {s.hintFacts.size} facts"
  -- errors
  let s ← startOn "mpd"
  match ← s.goalText spec "ph ->" with
  | .ok _ => check "hints: an unfinished statement is refused" false
  | .error msg => check "hints: an unfinished statement is refused" (contains msg "the formula ends here") msg
  match ← s.goalText spec "_" with
  | .ok _ => check "hints: a statement that is only a hole is refused" false
  | .error msg => check "hints: a statement that is only a hole is refused" (contains msg "only a hole") msg

end Tests.Prove
