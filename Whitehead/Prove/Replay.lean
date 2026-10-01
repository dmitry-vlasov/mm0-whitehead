/-
The replay test: every proof of a file is reduced to the tree of the assertions it uses
(`Db.skeleton`), and the engine reconstructs it, finding all expressions by unification
(`oracle` in `Prove.lean`). The result is the file with the reconstructed proof bodies
in the place of the original ones.
-/
import Whitehead.Mmb.Write
import Whitehead.Prove.Prove

namespace Whitehead.Prove

open Whitehead.Mmb

structure ReplayOptions where
  /-- The theorems to replay: those with numbers in `[first, last)`. -/
  first : Nat := 0
  last : Nat := 1000000000
  /-- Proofs with more steps than this, counted as a tree, are left out. -/
  maxSteps : Nat := 1000000000
  /-- Report every theorem that is not reconstructed. -/
  verbose : Bool := false

structure ReplayStats where
  /-- Theorems with a proof in the range. -/
  theorems : Nat := 0
  replayed : Nat := 0
  failed : Nat := 0
  /-- Left out: the proof uses a conversion, or is larger than `maxSteps`. -/
  conversions : Nat := 0
  tooLarge : Nat := 0
  /-- Steps of the known proofs that were replayed, and of the reconstructed ones. -/
  stepsIn : Nat := 0
  stepsOut : Nat := 0
  /-- Bytes of the original bodies of the replayed theorems, and of the new ones. -/
  bytesIn : Nat := 0
  bytesOut : Nat := 0
  /-- Proofs that reached the root and that the verifier did not accept. -/
  rejected : Nat := 0
  counters : Counters := {}

/-- Replays the proofs of `db.file`. Returns the statistics and, for every statement of
the file, the new proof body if its proof was reconstructed. -/
def replay (db : Db) (opts : ReplayOptions) (log : String → IO Unit) :
    IO (ReplayStats × Array (Option ByteArray)) := do
  let f := db.file
  let vc := Verify.Ctx.ofFile f
  let index := db.index
  let mut stats : ReplayStats := {}
  let mut bodies : Array (Option ByteArray) := Array.replicate f.stmts.size none
  for i in [0:f.stmts.size] do
    let s := f.stmts[i]!
    let isThm := match s.kind with
      | .thm _ => true
      | _ => false
    if !isThm || s.index < opts.first || s.index ≥ opts.last then continue
    stats := { stats with theorems := stats.theorems + 1 }
    let name := f.thmName s.index
    match db.skeleton s with
    | .error msg => throw (IO.userError s!"theorem {name}: {msg}")
    | .ok none => stats := { stats with conversions := stats.conversions + 1 }
    | .ok (some skel) =>
      let steps := skel.size (opts.maxSteps + 1)
      if steps > opts.maxSteps then
        stats := { stats with tooLarge := stats.tooLarge + 1 }
        continue
      let env := Env.init db index (db.task s.index)
      let result ← search vc env (oracle skel)
      let c := result.env.counters
      let sum := stats.counters
      stats := { stats with
        rejected := stats.rejected + result.rejected,
        counters := { props := sum.props + c.props, expanded := sum.expanded + c.expanded,
                      tuples := sum.tuples + c.tuples, notUnified := sum.notUnified + c.notUnified,
                      disjoint := sum.disjoint + c.disjoint, inconsistent := sum.inconsistent + c.inconsistent,
                      duplicate := sum.duplicate + c.duplicate } }
      match result.body, result.proof with
      | some body, some tree =>
        bodies := bodies.set! i (some body)
        stats := { stats with replayed := stats.replayed + 1, stepsIn := stats.stepsIn + steps,
                              stepsOut := stats.stepsOut + tree.size,
                              bytesIn := stats.bytesIn + (s.stop - s.bodyStart), bytesOut := stats.bytesOut + body.size }
      | _, _ =>
        stats := { stats with failed := stats.failed + 1 }
        if opts.verbose then
          let why := match result.ending with
            | .proved => "proved"
            | .exhausted => "the tree has no proof"
            | .limit => "limit reached"
          log s!"not replayed: theorem {s.index} {name} ({steps} steps): {why}; \
            {c.props} assertion nodes, {c.tuples} tuples, {c.notUnified} not unified, {c.disjoint} disjointness, \
            {c.inconsistent} inconsistent, {result.rejected} rejected by the verifier\
            {if result.rejection.isEmpty then "" else ": " ++ result.rejection}"
          if let some tree := result.rejectedProof then
            log s!"  goal: {db.showExp env.task.goal}\n  premises: {env.task.premises.map (db.showExp ·)}\n{tree.render db "  "}"
  return (stats, bodies)

/-! ### The search test -/

structure SearchOptions where
  first : Nat := 0
  last : Nat := 1000000000
  /-- Only every `every`-th theorem of the range: a sample. -/
  every : Nat := 1
  /-- `"bfs"`: the backward tree, breadth first; `"forward"`: the forward front alone;
  `"both"`: a round of the one and a wave of the other in turn. -/
  strategy : String := "bfs"
  limits : Limits := {}
  /-- Report every theorem. -/
  verbose : Bool := false

/-- What the search test reports for one theorem. -/
structure SearchRow where
  thm : Nat
  name : String
  ending : Ending
  /-- The steps of the proof found, and of the proof in the file. -/
  steps : Nat
  knownSteps : Nat
  ms : Nat
  props : Nat
  rejected : Nat
  /-- Facts of the forward front, and joins of a fact with a subgoal or the goal. -/
  facts : Nat := 0
  joins : Nat := 0

/-- Searches for a proof of every theorem of `db.file` in the range, each from the
assertions before it, with the strategy of `opts`. Returns a row per theorem and the new
proof bodies. -/
def searchAll (db : Db) (opts : SearchOptions) (log : String → IO Unit) :
    IO (Array SearchRow × Array (Option ByteArray)) := do
  let f := db.file
  let vc := Verify.Ctx.ofFile f
  let index := db.index
  let hypIndexes := if opts.strategy == "bfs" then {} else db.hypIndexes
  let mut rows : Array SearchRow := #[]
  let mut bodies : Array (Option ByteArray) := Array.replicate f.stmts.size none
  for i in [0:f.stmts.size] do
    let s := f.stmts[i]!
    let isThm := match s.kind with
      | .thm _ => true
      | _ => false
    if !isThm || s.index < opts.first || s.index ≥ opts.last || s.index % opts.every != 0 then continue
    let known := match db.skeleton s with
      | .ok (some skel) => skel.size
      | _ => 0
    let start ← IO.monoMsNow
    let env := Env.init db index (db.task s.index) hypIndexes
    let result ←
      if opts.strategy == "forward" then search vc env forwardOnly opts.limits
      else if opts.strategy == "both" then search vc env bidirectional opts.limits
      else search vc env breadthFirst opts.limits
    let ms := (← IO.monoMsNow) - start
    let steps := (result.proof.map (·.size)).getD 0
    if let some body := result.body then bodies := bodies.set! i (some body)
    let row : SearchRow :=
      { thm := s.index, name := f.thmName s.index, ending := result.ending, steps, knownSteps := known, ms,
        props := result.env.props.size, rejected := result.rejected,
        facts := result.env.counters.facts, joins := result.env.counters.joins }
    rows := rows.push row
    if opts.verbose then
      let what := match result.ending with
        | .proved => s!"proved in {steps} steps (the file has {known})"
        | .exhausted => "nothing left to expand"
        | .limit => "limit reached"
      log s!"{row.name}: {what}; {row.props} assertion nodes, {ms} ms\
        {if row.rejected == 0 then "" else s!", {row.rejected} proofs rejected by the verifier"}\
        {if opts.strategy == "bfs" then "" else s!", {row.facts} facts, {row.joins} joins"}"
  return (rows, bodies)

end Whitehead.Prove
