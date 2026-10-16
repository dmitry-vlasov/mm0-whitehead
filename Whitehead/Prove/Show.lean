/-
Printing the prover's expressions and proofs in the notation of the `.mm0` specification,
for the front-ends (`docs/DESIGN.md`, "Phase 4", "The session": "The server prints
expressions in `.mm0` notation").

The printer inverts the tables of the secondary parser (`Mm0/Math.lean`). A term with an
infix notation is printed between its arguments, one with a prefix notation or a general
`notation` as its literals say, a coercion as its argument alone, and any other as its
name applied to its arguments. Parentheses are put where the precedences ask for them, as
the grammar of `mm0.md` reads them back. A term of the proof file that the specification
does not have, a local definition, is printed by its name.
-/
import Whitehead.Prove.Pattern
import Whitehead.Prove.Tree

namespace Whitehead.Prove

open Whitehead.Mm0

/-- How a term of the proof file is printed. -/
inductive TermNotation where
  | infix (token : String) (prec : Nat) (rassoc : Bool)
  | prefix (token : String) (prec : Prec) (lits : Array Literal)
  | coercion
  | plain (name : String)
  deriving Inhabited

structure Printer where
  /-- By the number of a term of the proof file. -/
  terms : Std.HashMap Nat TermNotation := {}
  /-- The names of the variables of the theorem, the constants of its task. -/
  constNames : Array String := #[]

/-- The printer for the terms of `db`, with the notations of `spec`, and `constNames` for
the variables of the theorem being proved. -/
def Notation.printer (spec : Notation) (db : Db) (constNames : Array String := #[]) : Printer := Id.run do
  let math := spec.st.math
  let mut terms : Std.HashMap Nat TermNotation := {}
  for t in [0:db.terms.size] do
    terms := terms.insert t (.plain db.terms[t]!.name)
  let file (t : Nat) : Nat := spec.terms[t]?.getD t
  for t in [0:spec.st.env.terms.size] do
    terms := terms.insert (file t) (.plain spec.st.env.terms[t]!.name)
  for (_, path) in math.coes.toArray do
    for t in path do
      terms := terms.insert (file t) .coercion
  for (token, info) in math.prefixes.toArray do
    terms := terms.insert (file info.term) (.prefix token (math.consts[token]?.getD .max) info.lits)
  for (token, info) in math.infixes.toArray do
    let q := match math.consts[token]? with
      | some (.num q) => q
      | _ => 0
    terms := terms.insert (file info.term) (.infix token q info.rassoc)
  return { terms, constNames }

/-- The names of the binders of theorem `thm` of the proof file, from the specification. -/
def Notation.binderNames (spec : Notation) (thm : Nat) : Array String :=
  match spec.specThm thm with
  | some t => spec.st.env.thms[t]!.args.map fun v => v.name.getD "_"
  | none => #[]

namespace Printer

/-- The expression at node `i` of `e`, at precedence `p` or above: in parentheses if its
own is lower. `varName` names the variables. -/
partial def showAt (pr : Printer) (varName : Nat → String) (e : Exp) (i : Nat) (p : Prec) : String :=
  let n := e.nodes[i]!
  let wrap (level : Prec) (s : String) : String := if p.le level then s else s!"({s})"
  if Node.isVar n then varName (Node.varId n)
  else if Node.isConst n then (pr.constNames[Node.appId n - Node.constBase]?).getD s!"c{Node.appId n - Node.constBase}"
  else
    let args := e.argStarts i
    match pr.terms[Node.appId n]?.getD (.plain s!"t{Node.appId n}") with
    | .coercion => if h : 0 < args.size then pr.showAt varName e args[0] p else "?"
    | .infix token q rassoc =>
      let l := pr.showAt varName e args[0]! (.num (if rassoc then q + 1 else q))
      let r := pr.showAt varName e args[1]! (.num (if rassoc then q else q + 1))
      wrap (.num q) s!"{l} {token} {r}"
    | .prefix token q lits =>
      let parts := lits.map fun
        | .const tok => tok
        | .var idx prec => pr.showAt varName e args[idx]! prec
      wrap q (" ".intercalate (token :: parts.toList))
    | .plain name =>
      if args.isEmpty then name
      else wrap Prec.app (" ".intercalate (name :: (args.map (pr.showAt varName e · .max)).toList))

/-- An expression in the notation. A variable of the tree is `?` and a number, or what
`varName` says. -/
def render (pr : Printer) (e : Exp) (varName : Nat → String := fun v => s!"?{v}") : String :=
  if e.nodes.isEmpty then "" else pr.showAt varName e 0 (.num 0)

end Printer

/-! ### Proofs -/

/-- The statement that each step of a proof proves, for the theorem with premises
`premises`: an assertion's conclusion with the expressions given for its binders; a
premise; and for an unfolding, the statement of the step below with the def put in
(unfold) or its value (fold) at the path. -/
partial def ProofTree.statement (db : Db) (premises : Array Exp) : ProofTree → Exp
  | .hyp i => premises[i]?.getD default
  | .step a args _ =>
    let rule := db.asserts[a]!
    let image (k : Nat) : Exp := args[k]?.getD (Exp.ofVar rule.vars[k]!)
    let map : Std.HashMap Nat SubExp := (Array.range rule.vars.size).foldl (init := {}) fun m k =>
      m.insert (Node.varId rule.vars[k]!) (SubExp.mk' rule.vars[k]! (image k))
    ({ map } : Subst).apply rule.concl
  | .conv t path unfold args dummies child =>
    let below := child.statement db premises
    match below.nodeAt path with
    | none => below
    | some i =>
      let r := if unfold then Exp.mkApp t db.terms[t]!.ty args else db.unfolded t args dummies
      below.replace i r

/-- A proof as numbered steps, the premises of the theorem first, each step with the
numbers of the steps it uses and its statement in the notation. -/
def ProofTree.lines (db : Db) (pr : Printer) (premises : Array Exp) (t : ProofTree) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut stack : Array (ProofTree × Bool) := #[(t, false)]
  let mut done : Array Nat := #[]
  -- an explicit post-order walk: a step is numbered after the steps it uses
  while h : 0 < stack.size do
    let (node, visited) := stack[stack.size - 1]
    stack := stack.pop
    let children := match node with
      | .hyp _ => #[]
      | .step _ _ cs => cs
      | .conv _ _ _ _ _ c => #[c]
    if !visited && !children.isEmpty then
      stack := stack.push (node, true)
      for c in children.reverse do
        stack := stack.push (c, false)
    else
      let uses := done.extract (done.size - children.size) done.size
      done := done.extract 0 (done.size - children.size)
      let k := out.size + 1
      let what := match node with
        | .hyp i => s!"hypothesis {i}"
        | .step a _ _ => db.asserts[a]!.name
        | .conv t _ unfold _ _ _ => s!"{if unfold then "unfold" else "fold"} {db.terms[t]!.name}"
      let refs := if uses.isEmpty then "" else " " ++ ", ".intercalate (uses.map toString).toList
      out := out.push s!"{k}: {what}{refs} |- {pr.render (node.statement db premises)}"
      done := done.push k
  return out

end Whitehead.Prove
