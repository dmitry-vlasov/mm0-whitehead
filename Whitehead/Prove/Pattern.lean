/-
Patterns over the statements of the proof variant tree, written in the notation of the
`.mm0` specification (`docs/DESIGN.md`, "Phase 4", "Filters").

A pattern is a formula of the specification with holes: `$ _ -> ( _ -> _ ) $`. A hole
`_` matches any subexpression. The variables of the theorem being proved are what they
are in its task: constants, or the variables that stand for the binders marked as
metavariables. A pattern matches a statement at its top, node for node, the holes
aside. A variable of the statement that is not one of the theorem's is matched by a
hole only: the pattern says what the statement looks like, and nothing is unified.

The specification and the proof file number the terms differently, since the proof
file also has the local definitions; `Notation` keeps the correspondence, found by the
walk of `matchSpec` (`Verify/Spec.lean`). Sorts are the same in both.
-/
import Whitehead.Mm0.Elab
import Whitehead.Verify.Spec
import Whitehead.Prove.Db

namespace Whitehead.Prove

open Whitehead.Mm0 Whitehead.Mmb

/-- The variable that a hole of a pattern is. No variable of the tree has this number. -/
def holeId : Nat := 0xFFFFFFF

def holeNode : Nat := Node.var holeId 0

/-- The specification of a proof file, read for its notations. -/
structure Notation where
  st : ElabState
  /-- For each term of the specification, its number in the proof file. -/
  terms : Array Nat
  /-- For each axiom and theorem of the specification, its number in the proof file. -/
  thms : Array Nat
  deriving Inhabited

namespace Notation

/-- The notation of the specification `st`, which the proof file `f` proves. The walk is
that of `Verify.matchSpec`, without the matching: run `matchSpec` for that. -/
def ofSpec (st : ElabState) (f : MmbFile) : Notation := Id.run do
  let env := st.env
  let mut terms := Array.replicate env.terms.size 0
  let mut thms := Array.replicate env.thms.size 0
  let mut next := 0
  for s in f.stmts do
    let isLocal := match s.kind with
      | .termDef l | .thm l => l
      | _ => false
    if isLocal then continue
    let some decl := env.order[next]? | break
    next := next + 1
    match s.kind, decl with
    | .termDef _, .term i => terms := terms.set! i s.index
    | .ax, .thm i | .thm _, .thm i => thms := thms.set! i s.index
    | _, _ => pure ()
  return { st, terms, thms }

/-- The theorem of the specification that is theorem `thm` of the proof file. -/
def specThm (n : Notation) (thm : Nat) : Option Nat :=
  n.thms.findIdx? (· == thm)

/-- The names that the specification gives to the assertions of the proof file. -/
def names (n : Notation) : Array (Nat × String) :=
  (Array.range n.thms.size).map fun i => (n.thms[i]!, n.st.env.thms[i]!.name)

/-- An expression of the specification as an expression of the prover: variable `i` is
`vars i`, and the hole `hole` is the hole. -/
partial def toExp (n : Notation) (vars : Nat → Exp) (hole : Nat) : Mm0.Expr → Exp
  | .var i => if i == hole then ⟨#[holeNode]⟩ else vars i
  | .app t args =>
    let decl := n.st.env.terms[t]!
    Exp.mkApp n.terms[t]! (Ty.mk decl.retSort false) (args.map (toExp n vars hole))

/-- Reads the pattern `text`, the inside of `$ ... $`, for theorem `thm` of the proof file,
whose variables are `vars` in its task. `pos` is where the opening `$` is, for the
positions of errors. -/
def pattern (n : Notation) (thm : Nat) (vars : Nat → Exp) (text : String) (pos : Nat := 0) :
    Except ParseError Exp := do
  let some t := n.specThm thm
    | throw ⟨pos, s!"assertion {thm} of the proof file is not in the specification"⟩
  let args := n.st.env.thms[t]!.args
  let c := { Elab.mathCtx n.st args with hole := some args.size }
  let m : MathString := { text, span := ⟨pos, pos + text.utf8ByteSize + 2⟩ }
  let e ← parseMath c m .any
  return n.toExp vars args.size e

/-- An expression of the specification as a statement of the prover, in which a hole is
a new variable: the `j`-th hole is variable `fresh + j`, with the type of the argument
it stands in (`ty` for the whole). The state counts the holes. -/
partial def toFormula (n : Notation) (vars : Nat → Exp) (hole fresh : Nat) (ty : Nat) :
    Mm0.Expr → StateM Nat Exp
  | .var i => do
    if i == hole then
      let j ← modifyGet fun j => (j, j + 1)
      return Exp.ofVar (Node.var (fresh + j) ty)
    else return vars i
  | .app t args => do
    let decl := n.st.env.terms[t]!
    let mut out := #[]
    for k in [0:args.size] do
      let b := decl.args[k]!
      out := out.push (← toFormula n vars hole fresh (Ty.mk b.sort b.bound) args[k]!)
    return Exp.mkApp n.terms[t]! (Ty.mk decl.retSort false) out

/-- Reads the statement `text`, the inside of `$ ... $`, for theorem `thm` of the proof
file, as `pattern` does; but a hole `_` is a new variable, a metavariable, numbered from
`fresh` on. Returns the statement and the number of holes. A statement of a provable
sort is asked for, as for a theorem. -/
def formula (n : Notation) (thm : Nat) (vars : Nat → Exp) (text : String) (pos fresh : Nat) :
    Except ParseError (Exp × Nat) := do
  let some t := n.specThm thm
    | throw ⟨pos, s!"assertion {thm} of the proof file is not in the specification"⟩
  let args := n.st.env.thms[t]!.args
  let c := { Elab.mathCtx n.st args with hole := some args.size }
  let m : MathString := { text, span := ⟨pos, pos + text.utf8ByteSize + 2⟩ }
  let e ← parseMath c m .provable
  if e == .var args.size then throw ⟨pos, "a statement that is only a hole has no sort"⟩
  return (n.toFormula vars args.size fresh 0 e).run 0

end Notation

/-! ### Matching -/

/-- Matches the subexpression of pattern `p` at node `i` with that of `e` at node `j`.
Returns where both end, or `none`. -/
partial def matchAt (p e : Exp) (i j : Nat) : Option (Nat × Nat) := do
  let pn ← p.nodes[i]?
  let en ← e.nodes[j]?
  if Node.isVar pn && Node.varId pn == holeId then return (i + 1, j + Node.len en + 1)
  if Node.isVar pn || Node.isVar en then
    if pn == en then return (i + 1, j + 1) else none
  if Node.appId pn != Node.appId en || Node.ty pn != Node.ty en then none
  let pEnd := i + Node.len pn + 1
  let eEnd := j + Node.len en + 1
  let mut pi := i + 1
  let mut ej := j + 1
  while pi < pEnd do
    let (pi', ej') ← matchAt p e pi ej
    pi := pi'
    ej := ej'
  if ej == eEnd then return (pEnd, eEnd) else none

/-- Does pattern `p` match the expression `e`? -/
def Exp.matchesPattern (e p : Exp) : Bool :=
  match matchAt p e 0 0 with
  | some (i, j) => i == p.size && j == e.size
  | none => false

end Whitehead.Prove
