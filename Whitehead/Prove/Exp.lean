/-
Expressions of the prover: a port of `RuExp` (`russell-flow/src/ru/src.flow`,
`src/ru/util/exp.flow`).

An expression is the array of its nodes in prefix order. A node is a variable or the
application of a term; an application carries the number of nodes of its arguments, so
that a subexpression is a slice and can be skipped in one step. This is the
representation that the unifier and the index of Russell work on, and they are ported
on it unchanged.

What differs from Russell:

- A node is one number (an `Array Nat` of small numbers is stored unboxed), with the
  fields below. There is no arity field: nothing here needs it.
- The *type* of a node is a sort and one more bit, which says that only names have this
  type: bound variables. A bound binder `{x: s}` of MM0 is a variable of type "names of
  sort `s`", a regular binder `(a: s)` is a variable of type `s`, and names are a
  subtype of their sort. This is the typing of substitutions of the paper (section 2.2),
  for which Russell has `ruSuperRule`; see `docs/DESIGN.md`, "Where MM0 differs".
- The variables of the statement being proved must not be replaced. Russell turns them
  into constants, rules without arguments (`ruMakeConstEnv` in `prover/core/util.flow`).
  Here they are applications without arguments whose number is `Node.constBase` or
  more.
-/

namespace Whitehead.Prove

/-! ### Types -/

namespace Ty

/-- The type of the expressions of sort `sort`; with `name`, of its bound variables only. -/
@[inline] def mk (sort : Nat) (name : Bool) : Nat :=
  2 * sort + (if name then 1 else 0)

@[inline] def sort (ty : Nat) : Nat := ty / 2

@[inline] def isName (ty : Nat) : Bool := ty % 2 == 1

/-- May a variable of type `v` be replaced by an expression of type `e`? Only by the
same sort; and a name only by a name. -/
@[inline] def fits (v e : Nat) : Bool :=
  v == e || v + 1 == e && v % 2 == 0

end Ty

/-! ### Nodes

Bit 0 is set for a variable; bits 1–8 are the type. A variable has its number from bit
9 on. An application has the number of its term in bits 9–32 and the number of nodes of
its arguments from bit 33 on. The fields are taken apart as `UInt64`: see the note on
`Nat` literals in `Verify/Machine.lean`. -/

namespace Node

@[inline] def var (id ty : Nat) : Nat :=
  ((1 : UInt64) ||| (ty.toUInt64 <<< 1) ||| (id.toUInt64 <<< 9)).toNat

@[inline] def app (id ty len : Nat) : Nat :=
  ((ty.toUInt64 <<< 1) ||| (id.toUInt64 <<< 9) ||| (len.toUInt64 <<< 33)).toNat

@[inline] def isVar (n : Nat) : Bool := n.toUInt64 &&& 1 != 0

@[inline] def ty (n : Nat) : Nat := ((n.toUInt64 >>> 1) &&& 0xFF).toNat

/-- The number of a variable. -/
@[inline] def varId (n : Nat) : Nat := (n.toUInt64 >>> 9).toNat

/-- The number of the term of an application. -/
@[inline] def appId (n : Nat) : Nat := ((n.toUInt64 >>> 9) &&& 0xFFFFFF).toNat

/-- The number of nodes of the arguments of an application; `0` for a variable. -/
@[inline] def len (n : Nat) : Nat :=
  if n.toUInt64 &&& 1 != 0 then 0 else (n.toUInt64 >>> 33).toNat

/-- The application `n` with another length. -/
@[inline] def setLen (n len : Nat) : Nat :=
  ((n.toUInt64 &&& (0x1FFFFFFFF : UInt64)) ||| (len.toUInt64 <<< (33 : UInt64))).toNat

/-- Term numbers from here on stand for the variables of the statement being proved. -/
def constBase : Nat := 0x800000

/-- The limits of the fields. -/
def maxAppId : Nat := 0xFFFFFF
def maxLen : Nat := 0x3FFFFFFF

/-- The constant for variable `k` of the statement being proved. -/
@[inline] def const (k ty : Nat) : Nat := app (constBase + k) ty 0

@[inline] def isConst (n : Nat) : Bool := !isVar n && appId n ≥ constBase

end Node

/-! ### Expressions -/

structure Exp where
  nodes : Array Nat
  deriving BEq, Hashable, Inhabited

namespace Exp

@[inline] def size (e : Exp) : Nat := e.nodes.size

/-- The expression that is the variable `v` (a variable node). -/
@[inline] def ofVar (v : Nat) : Exp := ⟨#[v]⟩

/-- The type of an expression: that of its first node (`ruExpType`). -/
@[inline] def ty (e : Exp) : Nat := Node.ty e.nodes[0]!

/-- `ruIsVar` -/
@[inline] def isVar (e : Exp) : Bool := e.nodes.size == 1 && Node.isVar e.nodes[0]!

/-- Is `e` exactly the variable node `v`? (`e.nodes == [v]`) -/
@[inline] def isTheVar (e : Exp) (v : Nat) : Bool := e.nodes.size == 1 && e.nodes[0]! == v

/-- The subexpression that starts at node `i`. -/
@[inline] def sub (e : Exp) (i : Nat) : Exp :=
  ⟨e.nodes.extract i (i + Node.len e.nodes[i]! + 1)⟩

/-- The application of term `id`, of type `ty`, to `args`. -/
def mkApp (id ty : Nat) (args : Array Exp) : Exp := Id.run do
  let len := args.foldl (· + ·.size) 0
  let mut nodes := (Array.mkEmpty (len + 1)).push (Node.app id ty len)
  for a in args do
    nodes := nodes ++ a.nodes
  return ⟨nodes⟩

/-- The variable nodes of `e`, each once, in the order of their first occurrence
(`ruExp2Vars`). -/
def vars (e : Exp) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for n in e.nodes do
    if Node.isVar n && !out.contains n then out := out.push n
  return out

/-- Does the variable with number `id` occur in `e`? -/
def hasVar (e : Exp) (id : Nat) : Bool :=
  e.nodes.any fun n => Node.isVar n && Node.varId n == id

/-- Has `e` any variable? -/
def hasVars (e : Exp) : Bool :=
  e.nodes.any Node.isVar

/-- Is `e` well-formed as an array: every application's length stays inside it, and
the lengths nest? Used by tests and assertions; arities are checked where the terms are
known. -/
partial def wellFormed (e : Exp) : Bool :=
  e.nodes.size > 0 && go 0 e.nodes.size == some e.nodes.size
where
  /-- Reads one expression at `i` that must end before `stop`; returns where it ends. -/
  go (i stop : Nat) : Option Nat :=
    if i ≥ stop then none
    else
      let n := e.nodes[i]!
      if Node.isVar n then some (i + 1)
      else
        let last := i + 1 + Node.len n
        if last > stop then none else args (i + 1) last
  /-- Reads expressions from `i` until exactly `stop`. -/
  args (i stop : Nat) : Option Nat :=
    if i == stop then some stop
    else
      match go i stop with
      | some j => args j stop
      | none => none

/-- The expression as an s-expression, with the names given by `term` and `var` (which
get the number of a term and the number of a variable). -/
partial def toSexp (e : Exp) (term : Nat → String) (var : Nat → String) : String :=
  (go 0).1
where
  go (i : Nat) : String × Nat :=
    let n := e.nodes[i]!
    if Node.isVar n then (var (Node.varId n), i + 1)
    else if Node.len n == 0 then (term (Node.appId n), i + 1)
    else Id.run do
      let stop := i + 1 + Node.len n
      let mut out := "(" ++ term (Node.appId n)
      let mut j := i + 1
      while j < stop do
        let (s, k) := go j
        out := out ++ " " ++ s
        j := k
      return (out ++ ")", stop)

end Exp

end Whitehead.Prove
