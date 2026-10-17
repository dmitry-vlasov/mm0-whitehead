/-
Tests of the composable tactics (`Prove/Cost.lean`, `Prove/Rails.lean`, `Prove/Dsl.lean`;
`docs/DESIGN.md`, "Composable tactics") on `tests/fixtures/prove/logic.mmb`: the labels
of the nodes; `search`, which with `depth` builds breadth-first's tree; `bfs` with its
filter and limits; `first`; `follow`; the definitions, read from `tactics/` and from
text, with their errors; and `rails` and `replay`, written as definitions, which build
the trees that the strategies of the same names built.
-/
import Whitehead.Prove.Session
import Tests.Prove.Engine
import Tests.Prove.RailsRef

open Whitehead.Mmb Whitehead.Prove

namespace Tests.Prove

def tacticsTests : TestM Unit := do
  let bytes ← IO.FS.readBinFile logicPath
  let some file := MmbFile.parse bytes |>.toOption | check "tactics: the fixture is read" false; return
  let some db := Db.ofFile file |>.toOption | check "tactics: the fixture becomes a database" false; return
  let vc := Whitehead.Verify.Ctx.ofFile file
  let rails := Rails.ofDb db
  let index := db.index
  let id := thmId db
  let defs ← match ← Dsl.loadDefs "tactics" with
    | .ok d => pure d
    | .error e => check "tactics: the definitions of tactics/ are read" false e; return
  check "tactics: the definitions of tactics/ are read"
    (defs.contains "rails" && defs.contains "replay" && defs.contains "guided")
  let ctx : Dsl.Ctx := { db, rails := some rails, defs }
  let tac (text : String) : AnyStrategy :=
    match Dsl.parseTactic ctx text with
    | .ok t => t
    | .error _ => ⟨Strategy.done⟩
  let err (c : Dsl.Ctx) (text : String) : String :=
    match Dsl.parseTactic c text with
    | .ok _ => "accepted"
    | .error e => e.msg
  let thms := rails.sp.roots.map (·.1)
  let run (thm : Nat) (t : AnyStrategy) (n : Nat := 3000) : IO Result :=
    search vc (Env.init db index (db.task thm)) t.strategy { maxProps := n }
  -- the same tree: how the search ended, its proof, its nodes, and those it expanded, in order
  let same (a b : Result) : Bool :=
    a.ending == b.ending && (a.proof.map (proofText db)) == (b.proof.map (proofText db)) &&
      a.env.props.size == b.env.props.size && a.env.labels.map (·.1) == b.env.labels.map (·.1)
  let sameOn (a b : AnyStrategy) (n : Nat := 3000) : IO (Array String) := do
    let mut differ := #[]
    for thm in thms do
      if !same (← run thm a n) (← run thm b n) then differ := differ.push db.asserts[thm]!.name
    return differ
  -- labels: who expanded each node
  let r ← run (id "con1") (tac "bfs")
  check "tactics: bfs labels what it expands search"
    (!r.env.labels.isEmpty && r.env.labels.all (·.2 == .search) &&
      r.env.labels.size == r.env.counters.expanded)
  let mut both := 0
  let mut others := 0
  for thm in thms do
    let r ← run thm (tac "rails(3)")
    if r.env.labels.any (·.2 == .follow) && r.env.labels.any (·.2 == .search) then both := both + 1
    if r.env.labels.any fun (_, l) => l != .follow && l != .search then others := others + 1
  check "tactics: rails labels the steps of the replay follow, the others search" (both > 0 && others == 0)
    s!"{both} with both, {others} with others"
  let s ← Session.startFor vc (Env.init db index (db.task (id "a1i")))
  match s.variants 0 with
  | .error msg => check "tactics: a choice is labelled choose" false msg
  | .ok vs =>
    match vs.find? (·.name == "ax_mp") with
    | none => check "tactics: a choice is labelled choose" false "no ax_mp"
    | some mp =>
      match ← s.choose 0 #[mp.prop] with
      | .error msg => check "tactics: a choice is labelled choose" false msg
      | .ok s => check "tactics: a choice is labelled choose" (s.env.labels.contains (mp.prop, .choose))
  -- search: by depth, breadth-first round for round
  checkEq "tactics: search(depth) builds breadth-first's tree" (← sameOn (tac "bfs") (tac "search(depth)")) #[]
  checkEq "tactics: search is search(depth)" (← sameOn (tac "search") (tac "search(depth)")) #[]
  checkEq "tactics: depth(follow) without anything followed is depth"
    (← sameOn (tac "search(depth(follow, penalty=2))") (tac "search(depth)")) #[]
  -- ranked steps: a width past every rank is the depth; a width of 1 takes the first
  -- variant by the rank first
  let uses := Uses.ofFile file db.asserts.size
  let runU (thm : Nat) (t : AnyStrategy) (n : Nat := 3000) : IO Result :=
    search vc { Env.init db index (db.task thm) with uses } t.strategy { maxProps := n }
  let mut differ := #[]
  for thm in thms do
    if !same (← runU thm (tac "search(depth(by=recent, width=1000000))")) (← runU thm (tac "bfs")) then
      differ := differ.push db.asserts[thm]!.name
  checkEq "tactics: ranked steps, with a width past every rank, are the depth" differ #[]
  let r ← runU (id "syl") (tac "search(depth(by=recent, width=1))")
  let env0 := { Env.init db index (db.task (id "syl")) with uses }
  let key (p : Nat) : Nat × Nat := match r.env.props[p]!.step with
    | .assertion a => (uses.latest a env0.task.limit, uses.before a env0.task.limit)
    | .conv .. => (0, 0)
  let rootKids := r.env.hyps[0]!.children
  let gt (a b : Nat × Nat) : Bool := a.1 > b.1 || a.1 == b.1 && a.2 > b.2
  let topKey := rootKids.foldl (init := (0, 0)) fun m q => if gt (key q) m then key q else m
  check "tactics: ranked by recency, width 1: the first step is the latest used variant of the root"
    (r.ending == .proved && (r.env.labels[0]?.map fun (p, _) => key p == topKey && r.env.props[p]!.parent == 0) == some true)
  let r ← runU (id "syl") (tac "search(depth(by=used, width=1))")
  check "tactics: ranked by uses, width 1, proves" (r.ending == .proved)
  checkEq "tactics: a rank without a width" (err ctx "search(depth(by=recent))") "`depth` with `by` needs a `width`"
  checkEq "tactics: a rank that is not one" (err ctx "search(depth(by=best, width=3))") "`by` is used or recent, not `best`"
  -- bfs with a filter and limits, as the combinators
  checkEq "tactics: bfs with its filter and limits is limited(filter(f, bfs))"
    (← sameOn (tac "bfs(filter=premises(max=1), size=500, depth=4)")
               (tac "limited(filter(premises(max=1), bfs), size=500, depth=4)")) #[]
  checkEq "tactics: search with its filter and limits"
    (← sameOn (tac "search(depth, premises(max=1), 500, 4)")
               (tac "limited(filter(premises(max=1), search(depth)), size=500, depth=4)")) #[]
  -- first: by order
  checkEq "tactics: first(done, bfs) is bfs" (← sameOn (tac "first(done, bfs)") (tac "bfs")) #[]
  checkEq "tactics: first(bfs, done) is bfs" (← sameOn (tac "first(bfs, done)") (tac "bfs")) #[]
  checkEq "tactics: first of one is it" (← sameOn (tac "first(bfs)") (tac "bfs")) #[]
  -- follow: the theorem's own proof, put down at the root, proves it
  let mut followed := 0
  for thm in thms do
    if (← run thm (tac "follow(proof, at=root)") 100000).ending == .proved then followed := followed + 1
  checkEq "tactics: follow(proof) proves every theorem" followed thms.size
  -- rails and replay as definitions build the trees of the strategies they were (`RailsRef.lean`)
  let refs : Array (String × AnyStrategy) := #[
    ("rails", ⟨Ref.rails rails {}⟩), ("rails(3)", ⟨Ref.rails rails {}⟩),
    ("rails(0)", ⟨Ref.rails rails { replay := { count := 0 } }⟩),
    ("rails(10, rank=reach, open=0, upto=1)", ⟨Ref.rails rails { replay := { count := 10, rank := .reach, maxOpen := 0 }, upto := 1 }⟩),
    ("rails(3, rank=size, min=3, upto=2, ground=false)",
      ⟨Ref.rails rails { replay := { rank := .size, minSize := 3 }, upto := 2, ground := false }⟩),
    ("rails(5, rank=small, source=recurring, upto=1)",
      ⟨Ref.rails rails { replay := { count := 5, rank := .small, source := .recurring }, upto := 1 }⟩),
    ("replay", ⟨Ref.replay rails {}⟩), ("replay(5, rank=size, min=3)", ⟨Ref.replay rails { count := 5, rank := .size, minSize := 3 }⟩),
    ("replay(3, at=root)", ⟨Ref.replay rails {} .root⟩),
    ("replay(10, rank=reach, open=0)", ⟨Ref.replay rails { count := 10, rank := .reach, maxOpen := 0 }⟩)]
  for (text, old) in refs do
    checkEq s!"tactics: {text} builds the tree of the strategy it was" (← sameOn (tac text) old) #[]
  -- the language
  let ok (text : String) : Bool := (Dsl.parseTactic ctx text).isOk
  check "tactics: the new components"
    (ok "search(depth(follow, choose, penalty=1), filter=hyp, size=10, depth=3)" &&
      ok "follow(subproofs(5, rank=reach, open=0), at=root, upto=1, ground=true, chain=true)" &&
      ok "first(follow(proof), search(depth(follow)), bfs)" && ok "bfs(size=100)" && ok "follow(proof)" &&
      ok "guided" && ok "guided(close=3, open=2, upto=0, penalty=1)")
  checkEq "tactics: follow without the subproofs" (err { db } "follow(proof)") "`follow` needs the subproofs of the file"
  checkEq "tactics: a label that is not one" (err ctx "search(depth(bfs))")
    "a label of `depth` is follow, choose or search, not `bfs`"
  checkEq "tactics: a cost in a tactic's place" (err ctx "first(depth)") "`depth` is a cost; a tactic is expected here"
  checkEq "tactics: a guide that is not one" (err ctx "follow(bfs)") "`bfs` is a tactic; a guide is expected here"
  checkEq "tactics: a parameter outside a definition" (err ctx "bfs(filter=@f)")
    "`@f` is a parameter of a definition, outside one"
  checkEq "tactics: first needs a tactic" (err ctx "first()") "expected a term, found `)`"
  -- definitions read from text
  let defOf (text : String) : Except String Dsl.Def := (Dsl.parseDef text).mapError (·.msg)
  let defErr (text : String) : String := match defOf text with
    | .ok _ => "accepted"
    | .error e => e
  checkEq "tactics: a body that names a parameter not there" (defErr "x(a) = bfs(filter=@b)")
    "`@b` is not a parameter of `x`"
  checkEq "tactics: a definition without `=`" (defErr "x(a) bfs") "expected `=` after the head of the definition"
  checkEq "tactics: a default that names a parameter" (defErr "x(a, b=@a) = bfs") "a default cannot name a parameter, `@a`"
  checkEq "tactics: a parameter twice" (defErr "x(a, a) = bfs") "the parameter `a` is there twice"
  checkEq "tactics: a parameter that is not a name" (defErr "x(3) = bfs") "a parameter is a name, or name=default"
  match defOf "-- a bounded search\n-- by depth\nq(m, n=200) = limited(bfs(filter=@f), size=@n, depth=@m)" with
  | .ok _ => check "tactics: a body's parameters are checked" false
  | .error _ => check "tactics: a body's parameters are checked" true
  let mut mine : Dsl.Defs := {}
  for text in #["-- a bounded search\n-- by depth\nq(m, n=200) = limited(bfs, size=@n, depth=@m)",
                "loose(f) = filter(or(@f, hyp), bfs)", "few = premises(max=1)", "me = me",
                "deep(d=3) = search(depth(follow, penalty=@d))", "broken = bfs(filter=nope)"] do
    match defOf text with
    | .ok d => mine := mine.insert d.name d
    | .error e => check s!"tactics: the definition `{text}` is read" false e
  checkEq "tactics: a definition's help is its comment lines" ((mine.get? "q").map (·.help)) (some "a bounded search by depth")
  checkEq "tactics: a definition's signature" ((mine.get? "q").map (·.signature)) (some "q(m, n=200)")
  let c2 := { ctx with defs := mine }
  checkEq "tactics: a definition called, by name and by default" (← sameOn (match Dsl.parseTactic c2 "q(m=4)" with
      | .ok t => t | .error _ => ⟨Strategy.done⟩) (tac "limited(bfs, size=200, depth=4)")) #[]
  checkEq "tactics: a definition called, by position" (← sameOn (match Dsl.parseTactic c2 "q(4, 300)" with
      | .ok t => t | .error _ => ⟨Strategy.done⟩) (tac "limited(bfs, size=300, depth=4)")) #[]
  checkEq "tactics: a definition without what it needs" (err c2 "q") "`q` needs `m`"
  checkEq "tactics: a definition given too much" (err c2 "q(1, 2, 3)") "`q` has 2 parameters"
  checkEq "tactics: a definition given what it has not" (err c2 "q(m=1, k=2)") "`q` has no parameter `k`"
  checkEq "tactics: a definition that calls itself" (err c2 "me") "`me`: the definitions call one another without end"
  check "tactics: definitions of filters and costs, called where those go"
    ((Dsl.parseTactic c2 "loose(few)").isOk && (Dsl.parseTactic c2 "filter(few, bfs)").isOk &&
      (Dsl.parseTactic c2 "deep(1)").isOk && (Dsl.parseFilter c2 "and(few, hyp)").isOk)
  check "tactics: a definition of a tactic is not a filter" (Dsl.parseTactic c2 "bfs(filter=loose(all))").toOption.isNone
  match Dsl.parseTactic c2 "first(bfs, broken)" with
  | .ok _ => check "tactics: an error in a body is shown at the call" false
  | .error e => checkEq "tactics: an error in a body is shown at the call" s!"{e.pos} {e.msg}" "11 unknown filter `nope`"
  -- definitions read from files
  let dir : System.FilePath := ".lake/test-tactics"
  let write (files : Array (String × String)) : IO Unit := do
    if ← dir.isDir then IO.FS.removeDirAll dir
    IO.FS.createDirAll dir
    for (n, t) in files do IO.FS.writeFile (dir / n) t
  let loadErr (files : Array (String × String)) : IO String := do
    write files
    match ← Dsl.loadDefs dir with
    | .ok _ => return "accepted"
    | .error e => return e
  checkEq "tactics: a file with an error, by line and column"
    (← loadErr #[("a.tac", "-- fine\na = bfs"), ("b.tac", "-- broken\nb(x) =\n  bfs(filter=@y)")])
    s!"{dir / "b.tac"}:3:14: `@y` is not a parameter of `b`"
  checkEq "tactics: a file that defines another name"
    (← loadErr #[("a.tac", "c = bfs")]) s!"{dir / "a.tac"}: it defines `c`, not `a`"
  checkEq "tactics: a file that defines a component"
    (← loadErr #[("bfs.tac", "bfs = search")]) s!"{dir / "bfs.tac"}: `bfs` is a component of the language"
  write #[("a.tac", "a = bfs"), ("notes.txt", "not a definition")]
  match ← Dsl.loadDefs dir with
  | .ok d => check "tactics: only the .tac files are read" (d.size == 1 && d.contains "a")
  | .error e => check "tactics: only the .tac files are read" false e
  IO.FS.removeDirAll dir
  -- help lists the definitions
  let h := Dsl.helpWith defs
  check "tactics: help lists the definitions with their signatures"
    (contains h "definitions (tactics/*.tac):" && contains h "rails(count=3" && contains h "replay(count=3")

end Tests.Prove
