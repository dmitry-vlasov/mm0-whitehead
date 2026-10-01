/-
What the tests of the prover share: a small language in the shape of set.mm, a reader
of s-expressions for it, a generator of random expressions, and a second unifier,
written on trees in the plainest way, to compare the ported one with.
-/
import Whitehead.Prove.Unify
import Tests.Harness

open Whitehead.Prove

namespace Tests.Prove

/-- The types of the test language: three sorts, and the names of the second. -/
def wff : Nat := Ty.mk 0 false
def setvar : Nat := Ty.mk 1 false
def name : Nat := Ty.mk 1 true
def cls : Nat := Ty.mk 2 false

/-- Terms with their result type and argument types; the variables of a statement being
proved (constants); and variables. Lower case `x y z` are names, `u w` are regular
variables of the same sort, as `cv` takes one. -/
structure Sig where
  terms : Array (String × Nat × Array Nat)
  consts : Array (String × Nat)
  vars : Array (String × Nat)

def sig : Sig where
  terms := #[("wi", wff, #[wff, wff]), ("wn", wff, #[wff]), ("wal", wff, #[name, wff]),
             ("wceq", wff, #[cls, cls]), ("cv", cls, #[setvar]), ("wtru", wff, #[])]
  consts := #[("ph", wff), ("ps", wff), ("X", name), ("Y", name), ("U", setvar), ("C", cls)]
  vars := #[("a", wff), ("b", wff), ("c", wff), ("d", wff), ("x", name), ("y", name),
            ("z", name), ("A", cls), ("B", cls), ("u", setvar), ("w", setvar)]

namespace Sig

def varNode (g : Sig) (id : Nat) : Nat := Node.var id g.vars[id]!.2

def termName (g : Sig) (id : Nat) : String :=
  if id ≥ Node.constBase then g.consts[id - Node.constBase]!.1 else g.terms[id]!.1

def varName (g : Sig) (id : Nat) : String :=
  match g.vars[id]? with
  | some v => v.1
  | none => s!"v{id}"

def tokens (s : String) : Array String := Id.run do
  let mut out := #[]
  let mut cur := ""
  for ch in s.toList do
    if ch == '(' || ch == ')' || ch == ' ' then
      if !cur.isEmpty then out := out.push cur
      cur := ""
      if ch != ' ' then out := out.push ch.toString
    else cur := cur.push ch
  if !cur.isEmpty then out := out.push cur
  return out

partial def parseAt (g : Sig) (toks : Array String) (i : Nat) : Except String (Exp × Nat) := do
  let some tok := toks[i]? | throw "unexpected end"
  if tok == "(" then
    let some head := toks[i + 1]? | throw "unexpected end"
    let some id := g.terms.findIdx? (·.1 == head) | throw s!"unknown term {head}"
    let mut args := #[]
    let mut j := i + 2
    while toks[j]? != some ")" do
      let (a, k) ← parseAt g toks j
      args := args.push a
      j := k
    if args.size != g.terms[id]!.2.2.size then throw s!"{head}: wrong number of arguments"
    return (Exp.mkApp id g.terms[id]!.2.1 args, j + 1)
  else if let some id := g.vars.findIdx? (·.1 == tok) then
    return (Exp.ofVar (g.varNode id), i + 1)
  else if let some k := g.consts.findIdx? (·.1 == tok) then
    return (⟨#[Node.const k g.consts[k]!.2]⟩, i + 1)
  else if let some id := g.terms.findIdx? (·.1 == tok) then
    return (Exp.mkApp id g.terms[id]!.2.1 #[], i + 1)
  else throw s!"unknown name {tok}"

/-- The expression written as an s-expression. A mistake in a test is a panic. -/
def exp (g : Sig) (s : String) : Exp :=
  match parseAt g (tokens s) 0 with
  | .ok (e, _) => e
  | .error msg => panic! s!"test expression `{s}`: {msg}"

def var (g : Sig) (s : String) : Nat :=
  match g.vars.findIdx? (·.1 == s) with
  | some id => g.varNode id
  | none => panic! s!"test variable `{s}`"

/-- The substitution with these bindings, put together without any check. -/
def sub (g : Sig) (bindings : List (String × String)) : Subst :=
  { map := bindings.foldl (init := {}) fun m (v, e) =>
      m.insert (Node.varId (g.var v)) (SubExp.mk' (g.var v) (g.exp e)) }

def showExp (g : Sig) (e : Exp) : String := e.toSexp g.termName g.varName

def showSub (g : Sig) (s : Subst) : String := s.toSexp g.termName g.varName

def showOpt (g : Sig) (s : Option Subst) : String :=
  match s with
  | some s => g.showSub s
  | none => "none"

end Sig

/-! ### Random expressions -/

structure Rng where
  state : UInt64
  deriving Inhabited

def Rng.below (r : Rng) (n : Nat) : Nat × Rng :=
  let s := r.state * 6364136223846793005 + 1442695040888963407
  ((s >>> 33).toNat % n, ⟨s⟩)

/-- A random expression of type `ty`, of depth at most `depth`, over the variables with
numbers in `[lo, hi)` and, if `consts`, the constants. -/
partial def genExp (g : Sig) (ty depth lo hi : Nat) (consts : Bool) (r : Rng) : Exp × Rng := Id.run do
  let vars := (Array.range g.vars.size).filter fun i => lo ≤ i && i < hi && Ty.fits ty g.vars[i]!.2
  let cs := if consts then (Array.range g.consts.size).filter fun k => Ty.fits ty g.consts[k]!.2 else #[]
  let terms := (Array.range g.terms.size).filter fun t =>
    g.terms[t]!.2.1 == ty && (depth > 0 || g.terms[t]!.2.2.isEmpty)
  let leaves := vars.size + cs.size
  let (pick, r) := r.below (leaves + 2 * terms.size + (if leaves + terms.size == 0 then 1 else 0))
  if pick < vars.size then return (Exp.ofVar (g.varNode vars[pick]!), r)
  if pick < leaves then
    let k := cs[pick - vars.size]!
    return (⟨#[Node.const k g.consts[k]!.2]⟩, r)
  if terms.isEmpty then
    -- nothing of this type at this depth: one level deeper there is
    return genExp g ty (depth + 1) lo hi consts r
  let t := terms[(pick - leaves) % terms.size]!
  let mut r := r
  let mut args := #[]
  for a in g.terms[t]!.2.2 do
    let (e, r') := genExp g a (depth - 1) lo hi consts r
    args := args.push e
    r := r'
  return (Exp.mkApp t ty args, r)

/-! ### A reference unifier

Robinson's algorithm on trees with a list of bindings, with the same rule for types:
a variable is bound to an expression whose type fits it, and of two variables the one of
the more general type is bound to the other. It shares no code with the port. -/

inductive Tree where
  | var (node : Nat)
  | app (node : Nat) (args : List Tree)
  deriving Inhabited, BEq

partial def Tree.ofExp (e : Exp) : Tree :=
  (go 0).1
where
  go (i : Nat) : Tree × Nat :=
    let n := e.nodes[i]!
    if Node.isVar n then (.var n, i + 1)
    else Id.run do
      let stop := i + 1 + Node.len n
      let mut args := #[]
      let mut j := i + 1
      while j < stop do
        let (t, k) := go j
        args := args.push t
        j := k
      return (.app n args.toList, stop)

def Tree.ty : Tree → Nat
  | .var n => Node.ty n
  | .app n _ => Node.ty n

abbrev Bindings := List (Nat × Tree)

partial def walk (b : Bindings) : Tree → Tree
  | .var n =>
    match b.lookup n with
    | some t => walk b t
    | none => .var n
  | t => t

partial def occurs (b : Bindings) (v : Nat) (t : Tree) : Bool :=
  match walk b t with
  | .var n => n == v
  | .app _ args => args.any (occurs b v)

partial def naiveUnify (b : Bindings) (t1 t2 : Tree) : Option Bindings :=
  match walk b t1, walk b t2 with
  | .var v, .var w =>
    if v == w then some b
    else if Ty.fits (Node.ty v) (Node.ty w) then some ((v, .var w) :: b)
    else if Ty.fits (Node.ty w) (Node.ty v) then some ((w, .var v) :: b)
    else none
  | .var v, t | t, .var v =>
    if !Ty.fits (Node.ty v) t.ty || occurs b v t then none else some ((v, t) :: b)
  | .app n1 a1, .app n2 a2 =>
    if Node.appId n1 != Node.appId n2 || a1.length != a2.length then none
    else (a1.zip a2).foldlM (init := b) fun b (x, y) => naiveUnify b x y

/-- The tree with all bindings applied. -/
partial def resolve (b : Bindings) (t : Tree) : Tree :=
  match walk b t with
  | .var n => .var n
  | .app n args => .app n (args.map (resolve b))

/-- The shape of a tree: its variables numbered in the order of their first occurrence,
with their types. Two most general unifiers give the same shape. -/
partial def shape (t : Tree) : String :=
  (go t #[]).1
where
  go (t : Tree) (seen : Array Nat) : String × Array Nat :=
    match t with
    | .var n =>
      match seen.findIdx? (· == n) with
      | some i => (s!"?{i}:{Node.ty n}", seen)
      | none => (s!"?{seen.size}:{Node.ty n}", seen.push n)
    | .app n args => Id.run do
      let mut out := s!"({Node.appId n}"
      let mut seen := seen
      for a in args do
        let (s, seen') := go a seen
        out := out ++ " " ++ s
        seen := seen'
      return (out ++ ")", seen)

end Tests.Prove
