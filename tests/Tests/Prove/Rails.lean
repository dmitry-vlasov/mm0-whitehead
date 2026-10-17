/-
Tests of the replay of subproofs (`Prove/Rails.lean`) on `tests/fixtures/prove/logic.mmb`:
the subproofs that fit a goal, only those of earlier proofs and as configured; a replay
that follows a proof step by step and reproduces it; one that does not fit and expands
nothing; one that leaves a goal open for the search to build up; `rails` without
subproofs, which is breadth-first round for round; `loop`; and the language.
-/
import Whitehead.Prove.Session
import Tests.Prove.Engine

open Whitehead.Mmb Whitehead.Prove

namespace Tests.Prove

def railsTests : TestM Unit := do
  let bytes ← IO.FS.readBinFile logicPath
  let some file := MmbFile.parse bytes |>.toOption | check "rails: the fixture is read" false; return
  let some db := Db.ofFile file |>.toOption | check "rails: the fixture becomes a database" false; return
  let vc := Whitehead.Verify.Ctx.ofFile file
  let id := thmId db
  let rails := Rails.ofDb db
  let index := db.index
  let envOf (name : String) : Env := Env.init db index (db.task (id name))
  -- replay and rails are definitions (tactics/*.tac)
  let defs ← match ← Dsl.loadDefs "tactics" with
    | .ok d => pure d
    | .error _ => pure {}
  let ctx : Dsl.Ctx := { db, rails := some rails, defs }
  let tac (text : String) : AnyStrategy :=
    match Dsl.parseTactic ctx text with
    | .ok t => t
    | .error _ => ⟨Strategy.done⟩
  -- the subproofs that fit a goal: of earlier proofs only, ranked, as many as asked
  let at0 (name : String) (cfg : ReplayConfig) : Array Nat :=
    let env := envOf name
    rails.at_ env 0 cfg
  let all := at0 "con1" { count := 1000, minSize := 1 }
  check "rails: only subproofs of the proofs before the theorem"
    (!all.isEmpty && all.all fun k => rails.sp.first[k]! < id "con1") s!"{all.size}"
  check "rails: as many as asked, from the size asked"
    ((at0 "con1" { count := 2 }).size ≤ 2 && (at0 "con1" { count := 1000, minSize := 3 }).all (rails.sp.sizes[·]! ≥ 3))
  let bySize := at0 "con1" { count := 1000, minSize := 1, rank := .size }
  check "rails: ranked by size, the largest first"
    ((Array.range (bySize.size - 1)).all fun j => rails.sp.sizes[bySize[j]!]! ≥ rails.sp.sizes[bySize[j + 1]!]!)
  let recurring := at0 "con1" { count := 1000, minSize := 1, source := .recurring }
  check "rails: recurring, those of two earlier proofs"
    (recurring.all fun k => rails.sp.occBefore k (id "con1") ≥ 2 && all.contains k)
  -- each theorem's own proof, put down at its root, is followed step by step and proves it
  let mut replayed := 0
  for (thm, root) in rails.sp.roots do
    let env := Env.init db index (db.task thm)
    let r ← search vc env (Strategy.replayFrom rails #[(0, root)]) { maxProps := 100000 }
    if r.ending == .proved then replayed := replayed + 1
  checkEq "rails: every proof, replayed, proves its theorem" replayed rails.sp.roots.size
  -- a subproof that does not fit: syl's proof at a1i, whose root has no variant for mpd
  match rails.sp.roots.find? (·.1 == id "syl") with
  | none => check "rails: syl's proof is read" false
  | some (_, sylProof) =>
    let r ← search vc (envOf "a1i") (Strategy.replayFrom rails #[(0, sylProof)]) { maxProps := 100000 }
    check "rails: a subproof that does not fit expands nothing" (r.env.counters.expanded == 0 && r.proof.isNone)
  -- mpd's proof at syl: its first premise is syl's premise ph -> ps, its second is left
  -- open, ph -> ps -> ch, and the search builds it up from ps -> ch
  match rails.sp.roots.find? (·.1 == id "mpd") with
  | none => check "rails: mpd's proof is read" false
  | some (_, mpdProof) =>
    let s := (⟨Strategy.replayFrom rails #[(0, mpdProof)]⟩ : AnyStrategy).seq (tac "search(depth)")
    let r ← search vc (envOf "syl") s.strategy { maxProps := 100000 }
    checkEq "rails: a rail with a goal left open, built up by the search"
      ((r.proof.map (proofText db)).getD "none") "(mpd h1 (a1i h0))"
    -- by depth(follow), the rail's step is free, read off its label: the goal it left open
    -- costs what the root's alternatives cost, and is built up in the same rounds
    let s := (⟨Strategy.replayFrom rails #[(0, mpdProof)]⟩ : AnyStrategy).seq (tac "search(depth(follow))")
    let r' ← search vc (envOf "syl") s.strategy { maxProps := 100000 }
    check "rails: the step of a rail followed before is free for the search after it"
      (r'.ending == .proved && r'.env.labels.any (·.2 == .follow) && r'.env.props.size ≤ r.env.props.size)
      s!"{r'.env.props.size} against {r.env.props.size} nodes"
  -- reach: mpd's lemma at syl, (a -> b), (a -> b -> c) => a -> c, leaves one hypothesis
  -- open: ph -> ps is syl's premise, ph -> ps -> ch is not
  match rails.sp.roots.find? (·.1 == id "mpd") with
  | none => pure ()
  | some (_, mpdProof) =>
    let env := envOf "syl"
    checkEq "rails: the hypotheses a subproof leaves open" (rails.openHyps env env.task.goal mpdProof) 1
  let reach := (envOf "con1") |> fun env => rails.at_ env 0 { count := 1000, minSize := 1, rank := .reach }
  let opens := reach.map fun k => rails.openHyps (envOf "con1") (envOf "con1").task.goal k
  check "rails: by reach, the fewest open first"
    ((Array.range (opens.size - 1)).all fun j => opens[j]! ≤ opens[j + 1]!) s!"{opens}"
  let closing := (envOf "con1") |> fun env => rails.at_ env 0 { count := 1000, minSize := 1, rank := .reach, maxOpen := 0 }
  check "rails: open=0 keeps those that leave nothing open"
    (closing.all fun k => rails.openHyps (envOf "con1") (envOf "con1").task.goal k == 0 &&
      closing.size == (opens.filter (· == 0)).size)
  -- rails without subproofs is breadth-first, round for round
  let mut same := true
  for (thm, _) in rails.sp.roots do
    let a ← search vc (Env.init db index (db.task thm)) breadthFirst { maxProps := 3000 }
    let b ← search vc (Env.init db index (db.task thm)) (tac "rails(0)").strategy { maxProps := 3000 }
    if a.ending != b.ending || (a.proof.map (proofText db)) != (b.proof.map (proofText db)) ||
        a.env.props.size != b.env.props.size then same := false
  check "rails: without subproofs, the same tree and proofs as breadth-first" same
  -- rails with subproofs: every proof found is checked by the verifier, as any
  let mut proved := 0
  for (thm, _) in rails.sp.roots do
    let r ← search vc (Env.init db index (db.task thm)) (tac "rails(3)").strategy { maxProps := 3000 }
    if r.ending == .proved && r.body.any (·.size > 0) then proved := proved + 1
  check "rails: with subproofs, theorems proved and verified" (proved ≥ 13) s!"{proved}"
  -- loop: the body again while the tree grows
  let r ← search vc (envOf "con1") ((breadthFirst.sized 100).loop 3) { maxProps := 100000 }
  check "rails: loop runs its body again" (r.env.props.size > 100) s!"{r.env.props.size}"
  -- the language
  let ok (text : String) : Bool := (Dsl.parseTactic ctx text).isOk
  check "rails: the tactics of the language"
    (ok "replay" && ok "replay(5, rank=size, min=3, source=recurring, at=root)" && ok "rails(3)" &&
      ok "rails(count=1, rank=small, upto=1, ground=false)" && ok "loop(seq(limited(bfs, size=100), rails(1)), 5)" &&
      ok "rails(10, rank=reach, open=0, penalty=2)")
  let err (c : Dsl.Ctx) (text : String) : String :=
    match Dsl.parseTactic c text with
    | .ok _ => "accepted"
    | .error e => e.msg
  checkEq "rails: without the subproofs" (err { db, defs } "rails(3)") "`follow` needs the subproofs of the file"
  checkEq "rails: a rank that is not one" (err ctx "rails(3, rank=best)") "`rank` is occurrences, size, small or reach, not `best`"
  checkEq "rails: a source that is not one" (err ctx "replay(source=all)") "`source` is earlier or recurring, not `all`"

end Tests.Prove
