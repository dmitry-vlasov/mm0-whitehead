/-
Checking a proof file against a specification: the last step of `verify`.

The proof file must declare, in order, what the specification declares: the same sorts
with the same modifiers, the same terms and definitions with the same binders, and
axioms and theorems with the same statements. Formulas are compared as trees: the
expression elaborated from the `.mm0` text against the unify stream of the proof file.
This is `env.extend` of the formal semantics (`mm0-lean/mm0/mm0.lean`).

`mm0-rs` has no counterpart of this check. mm0-c has one (`parser.c`).
-/
import Whitehead.Mm0.Env
import Whitehead.Verify.Check

namespace Whitehead.Verify

open Whitehead.Mm0 Whitehead.Mmb

/-- `sort wff`, `term imp`, `axiom ax_1`: a declaration of the specification. -/
def declLabel (env : Env) : DeclRef → String
  | .sort i => s!"sort {env.sorts[i]!.name}"
  | .term i => (if env.terms[i]!.isDef then "def " else "term ") ++ env.terms[i]!.name
  | .thm i => (if env.thms[i]!.isAxiom then "axiom " else "theorem ") ++ env.thms[i]!.name

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

/-- One public statement of the proof file against the declaration of the specification
at the same place. `termMap` gives, for each term of the specification so far, its
number in the proof file. Returns the proof file's number for a term or def. -/
def matchStmt (env : Env) (f : MmbFile) (termMap : Array Nat) (s : Mmb.Stmt) (decl : DeclRef) :
    Except String (Option Nat) := do
    match s.kind, decl with
    | .sort, .sort i =>
      let ours := env.sorts[i]!.mods
      let theirs := f.sorts[s.index]!
      if (ours.isPure, ours.isStrict, ours.isProvable, ours.isFree) !=
          (theirs.isPure, theirs.isStrict, theirs.isProvable, theirs.isFree) then
        throw s!"sort {env.sorts[i]!.name}: different modifiers"
      return none
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
      return some s.index
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
      return none
    | _, _ => throw s!"the .mm0 declares {declLabel env decl} here, the .mmb a statement of a different kind"

/-- Checks that the proof file proves the specification: its public statements, in
order, are the declarations of the specification, and nothing of the specification is
left over (`env.extend` in `mm0.lean`: local definitions and theorems may be added, a
definition may be given a value, and nothing else may differ). Returns the number of
statements compared. -/
def matchSpec (env : Env) (f : MmbFile) : Except VerifyError Nat := do
  let mut next := 0
  let mut termMap : Array Nat := #[]
  for i in [0:f.stmts.size] do
    let s := f.stmts[i]!
    let isLocal := match s.kind with
      | .termDef l | .thm l => l
      | _ => false
    if isLocal then continue
    let some decl := env.order[next]?
      | throw { pos := s.pos, stmt := some i,
                msg := s!"the specification has no statement for this one: all its {env.order.size} statements are used up" }
    next := next + 1
    match matchStmt env f termMap s decl with
    | .ok (some t) => termMap := termMap.push t
    | .ok none => pure ()
    | .error msg => throw { pos := s.pos, stmt := some i, msg := s!"does not match the specification: {msg}" }
  if next != env.order.size then
    throw { pos := f.header.pProof, stmt := none,
            msg := s!"the specification has {env.order.size} statements, the proof file declares only {next} of them; the next one is {declLabel env env.order[next]!}" }
  return next

end Whitehead.Verify
