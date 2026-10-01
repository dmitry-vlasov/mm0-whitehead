/-
The elaborator against proof files: for a `.mm0`/`.mmb` pair, every statement of the
specification, elaborated from its text, must be the statement that the proof file
declares at the same place — the same binders, and formulas that are the same trees as
the unify streams.

This compares two independent routes to the same data: ours through the notations of
the `.mm0` file, and that of the tool that wrote the `.mmb` file (`mm0-rs` or `mm0-hs`).
It is test code. The verifier will need the same comparison as one of its checks.
-/
import Whitehead.Mm0.Elab
import Whitehead.Mmb.Reader
import Tests.Harness

open Whitehead Whitehead.Mm0 Whitehead.Mmb

namespace Tests.Mm0

/-- The `deps` bit set of a `.mmb` binder for a list of variable indices: bit `j` for the
`j`-th bound variable. -/
def depsBits (args : Array VarDecl) (deps : Array Nat) : UInt64 := Id.run do
  let mut bits : UInt64 := 0
  let mut j : UInt64 := 0
  for i in [0:args.size] do
    if args[i]!.bound then
      if deps.contains i then bits := bits ||| ((1 : UInt64) <<< j)
      j := j + 1
  return bits

/-- The binders of a declaration against the `arg` words of the proof file. -/
def matchArgs (what : String) (ours : Array VarDecl) (theirs : Array Arg) : Except String Unit := do
  if ours.size != theirs.size then
    throw s!"{what}: {ours.size} arguments in the .mm0, {theirs.size} in the .mmb"
  let mut boundIdx : UInt64 := 0
  for i in [0:ours.size] do
    let a := ours[i]!
    let b := theirs[i]!
    if a.sort != b.sort || a.bound != b.bound then
      throw s!"{what}: argument {i} differs in sort or kind"
    if a.bound then
      if b.deps != (1 : UInt64) <<< boundIdx then
        throw s!"{what}: bound argument {i} does not have its own dependency bit"
      boundIdx := boundIdx + 1
    else if depsBits ours a.deps != b.deps then
      throw s!"{what}: argument {i} differs in its dependencies"

/-- A pattern of a unify stream against an expression of the specification. `heap` holds
the expression for every heap index of the stream so far; `nargs` is the number of
arguments, the variables above being dummies with the sorts `dummySorts`. `termMap`
gives, for a term of the specification, its number in the proof file, which also counts
the local definitions. -/
partial def matchPattern (termMap : Array Nat) (nargs : Nat) (dummySorts : Array Nat)
    (p : Pattern) (e : Expr) (heap : Array Expr) : Except String (Array Expr) := do
  match p with
  | .ref i =>
    if heap[i]? == some e then return heap
    else throw s!"a reference to heap entry {i} stands where the .mm0 has something else"
  | .dummy sort _ =>
    match e with
    | .var v =>
      if v < nargs then throw "a dummy in the .mmb stands where the .mm0 has an argument"
      if dummySorts[v - nargs]? != some sort then throw "a dummy has a different sort"
      -- a dummy of the stream is a new variable each time
      if heap.contains e then throw "two dummies of the .mmb are one variable in the .mm0"
      return heap.push e
    | _ => throw "a dummy in the .mmb stands where the .mm0 has a term"
  | .app t save args =>
    match e with
    | .app t' args' =>
      if termMap[t']? != some t || args.size != args'.size then
        throw s!"term {t} in the .mmb, term {termMap[t']?.getD t'} in the .mm0"
      let slot := heap.size
      let mut heap := if save.isSome then heap.push default else heap
      for i in [0:args.size] do
        heap ← matchPattern termMap nargs dummySorts args[i]! args'[i]! heap
      if save.isSome then heap := heap.set! slot e
      return heap
    | .var _ => throw s!"term {t} in the .mmb stands where the .mm0 has a variable"

/-- Every statement of the specification against the proof file. Returns the number of
statements compared. -/
def matchPair (env : Env) (f : MmbFile) : Except String Nat := do
  let mut next := 0
  let mut termMap : Array Nat := #[]
  for s in f.stmts do
    let isLocal := match s.kind with
      | .termDef l | .thm l => l
      | _ => false
    if isLocal then continue
    let some decl := env.order[next]?
      | throw s!"the .mmb has more public statements than the .mm0 ({env.order.size})"
    next := next + 1
    match s.kind, decl with
    | .sort, .sort i =>
      let ours := env.sorts[i]!.mods
      let theirs := f.sorts[s.index]!
      if (ours.isPure, ours.isStrict, ours.isProvable, ours.isFree) !=
          (theirs.isPure, theirs.isStrict, theirs.isProvable, theirs.isFree) then
        throw s!"sort {env.sorts[i]!.name}: different modifiers"
    | .termDef _, .term i =>
      let ours := env.terms[i]!
      let what := s!"term {ours.name}"
      let theirs := f.terms[s.index]!
      if ours.isDef != theirs.isDef then throw s!"{what}: a def on one side, a term on the other"
      matchArgs what ours.args (f.termArgs s.index)
      let ret := f.termRet s.index
      if ours.retSort != ret.sort || depsBits ours.args ours.retDeps != ret.deps then
        throw s!"{what}: different return type"
      if let some value := ours.value then
        match f.termValue s.index with
        | .error e => throw s!"{what}: 0x{hex e.pos}: {e.msg}"
        | .ok st =>
          let heap := (Array.range ours.args.size).map Expr.var
          match matchPattern termMap ours.args.size (value.dummies.map (·.sort)) st.concl value.expr heap with
          | .ok _ => pure ()
          | .error msg => throw s!"{what}: value: {msg}"
      -- only now can the term be referred to
      termMap := termMap.push s.index
    | .ax, .thm i | .thm _, .thm i =>
      let ours := env.thms[i]!
      let what := s!"{if ours.isAxiom then "axiom" else "theorem"} {ours.name}"
      if ours.isAxiom != (s.kind == .ax) then throw s!"{what}: an axiom on one side, a theorem on the other"
      matchArgs what ours.args (f.thmArgs s.index)
      match f.thmStatement s.index with
      | .error e => throw s!"{what}: 0x{hex e.pos}: {e.msg}"
      | .ok st =>
        if st.hyps.size != ours.hyps.size then
          throw s!"{what}: {ours.hyps.size} hypotheses in the .mm0, {st.hyps.size} in the .mmb"
        -- heap indices are assigned in stream order: the conclusion, then the
        -- hypotheses from the last to the first
        let mut heap := (Array.range ours.args.size).map Expr.var
        match matchPattern termMap ours.args.size #[] st.concl ours.concl heap with
        | .ok h => heap := h
        | .error msg => throw s!"{what}: conclusion: {msg}"
        for k in [0:st.hyps.size] do
          let j := st.hyps.size - 1 - k
          match matchPattern termMap ours.args.size #[] st.hyps[j]! ours.hyps[j]!.expr heap with
          | .ok h => heap := h
          | .error msg => throw s!"{what}: hypothesis {j}: {msg}"
    | _, _ => throw s!"statement {next - 1} of the .mm0 is of a different kind than its counterpart at 0x{hex s.pos}"
  if next != env.order.size then
    throw s!"the .mm0 has {env.order.size} statements, the .mmb only {next} public ones"
  return next

/-- Pairs of the corpus whose two files do not belong together. `hello_assembler.mm1` is
unfinished: where the specification declares `def hello`, the proof file has a theorem.
mm0-c rejects the pair at the same statement. -/
def knownMismatches : List String := ["hello_assembler"]

/-- Loads, elaborates and matches one pair. -/
def checkPair (mm0 mmb : System.FilePath) : TestM Nat := do
  let name := s!"pair: {mm0} = {mmb}"
  let mismatch := knownMismatches.contains (mm0.fileStem.getD "")
  match ← load mm0 with
  | .error e => check name false e.format; return 0
  | .ok spec =>
    match elaborate spec with
    | .error e => check name false e.format; return 0
    | .ok env =>
      match MmbFile.parse (← IO.FS.readBinFile mmb) with
      | .error e => check name false (e.format mmb.toString); return 0
      | .ok f =>
        match matchPair env f with
        | .error msg =>
          check name (mismatch && contains msg "different kind") msg
          return 0
        | .ok n =>
          check name (!mismatch) "matched, but it is listed as a known mismatch"
          return n

def pairTests : TestM Unit := do
  let mut total := 0
  let mut pairs := 0
  -- the fixtures of this repository
  let mut list : Array (System.FilePath × System.FilePath) := #[
    ("tests/fixtures/mmb/small.mm0", "tests/fixtures/mmb/small.mmb")]
  for n in ["bound_arg_vars", "regular_arg_vars", "sorry_expr", "sorry_conv", "local_term",
      "axiom_body_mismatch", "ret_sort_mismatch"] do
    list := list.push (s!"tests/fixtures/disputed/{n}.mm0", s!"tests/fixtures/disputed/{n}.mmb")
  -- the pairs of the MM0 repository that come with a compiled proof file
  match ← IO.getEnv "MM0_REPO" with
  | none => skip "pairs of the MM0 repository" "set MM0_REPO to a checkout"
  | some repo =>
    let root : System.FilePath := repo
    list := list ++ #[
      (root / "examples/hol.mm0", root / "mm0-js/test/hol.mmb"),
      (root / "examples/peano.mm0", root / "mm0-js/test/peano.mmb"),
      (root / "examples/tutorial/02-mm0-intro.mm0", root / "examples/tutorial/03-mm1-intro.mmb"),
      (root / "tests/mmb/pass/max_bound_vars.mm0", root / "tests/mmb/pass/max_bound_vars.mmb")]
  -- the built corpus
  let corpus : System.FilePath := ".tools/corpus"
  if ← corpus.isDir then
    let entries ← corpus.readDir
    let names := (entries.filterMap fun e =>
      if e.path.extension == some "mmb" then e.path.fileStem else none).qsort (· < ·)
    for n in names do
      list := list.push (corpus / s!"{n}.mm0", corpus / s!"{n}.mmb")
  else
    skip "pairs of .tools/corpus" "run scripts/build-corpus.sh"
  for (mm0, mmb) in list do
    let n ← checkPair mm0 mmb
    if n > 0 then
      pairs := pairs + 1
      total := total + n
  IO.println s!"pairs: {pairs} specifications elaborated and matched against their proof files, \
    {total} statements"

end Tests.Mm0
