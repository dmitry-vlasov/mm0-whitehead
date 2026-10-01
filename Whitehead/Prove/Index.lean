/-
The index of expressions: a port of `RuIndex` (`russell-flow/src/ru/index.flow`) and of
`ruUnifyIndex` (`src/ru/unify/index.flow`).

The index is a trie over the node arrays of the expressions put into it: a
discrimination tree. One step down the trie is one node of an expression, an
application by its term or a variable by itself. `unify` finds every stored expression
that unifies with a given one, with the unifier, in one walk: where the given expression
has an application, the walk follows the branch of the same term, and also every branch
of a variable, which is bound to the subexpression and skips it; where the given
expression has a variable, the walk takes every subexpression that starts in the trie
at that point.

For the last case a node knows where the subexpressions that start at it end (`ends`),
and a node where one ends knows how long it was (`lens`), from which the subexpression
is put together again (`subexpr`).

What differs from Russell:

- one array holds all nodes, and a node has the numbers of its children, where Russell
  has a hash map per level; a child is found by a scan of its siblings;
- a variable is a key with its type, not by its number alone: the binders of different
  assertions of MM0 share their numbers but not their types;
- an expression is put in by one walk down and one pass over its applications, not by
  recursion; the sets `ends` and `lens` come out the same;
- a variable is bound to an expression whose type fits it, and of two variables the more
  general is bound to the more special. Russell asks `ruSuperRule` here, with the two
  types in the other order than in `ruAdd2Subst1`.
-/
import Whitehead.Prove.Unify

namespace Whitehead.Prove

/-- `RuIndexNode` -/
structure IndexNode (α : Type) where
  /-- The node of the expressions that leads here: a variable node, or an application
  with its length set to 0. -/
  key : Nat
  parent : Nat
  /-- Children that are applications, and children that are variables. -/
  rules : Array Nat := #[]
  vars : Array Nat := #[]
  /-- The nodes at which a subexpression that starts here ends. -/
  ends : Array Nat := #[]
  /-- The lengths (as in `Node.len`) of the subexpressions that end here. -/
  lens : Array Nat := #[]
  /-- What is stored for the expressions that end here. -/
  data : Array α := #[]
  deriving Inhabited

/-- `RuIndex`. Node 0 is the root, which stands for no node of an expression. -/
structure Index (α : Type) where
  nodes : Array (IndexNode α) := #[{ key := 0, parent := 0 }]
  /-- The number of expressions put in. -/
  size : Nat := 0
  deriving Inhabited

namespace Index

variable {α : Type}

/-- The key of a node of an expression: an application without its length. -/
@[inline] def keyOf (n : Nat) : Nat :=
  if Node.isVar n then n else Node.setLen n 0

/-- The child of `parent` with this key among `kids`. -/
def findChild (ix : Index α) (kids : Array Nat) (key : Nat) : Option Nat :=
  kids.find? fun c => ix.nodes[c]!.key == key

/-- The child of `parent` for the application of term `id`, whatever its type. -/
def findRule (ix : Index α) (parent : Nat) (id : Nat) : Option Nat :=
  ix.nodes[parent]!.rules.find? fun c => Node.appId ix.nodes[c]!.key == id

/-- `ruSetIndex`: stores `data` under the expression `key`. -/
def insert (ix : Index α) (key : Exp) (data : α) : Index α := Id.run do
  let mut nodes := ix.nodes
  -- the path of the expression, a node of the trie for each of its nodes
  let mut path : Array Nat := Array.mkEmpty key.size
  let mut cur := 0
  for n in key.nodes do
    let k := keyOf n
    let isVar := Node.isVar n
    let kids := if isVar then nodes[cur]!.vars else nodes[cur]!.rules
    match kids.find? fun c => nodes[c]!.key == k with
    | some c => cur := c
    | none =>
      let c := nodes.size
      nodes := nodes.push { key := k, parent := cur }
      let parent := cur
      nodes := nodes.modify parent fun p =>
        if isVar then { p with vars := p.vars.push c } else { p with rules := p.rules.push c }
      cur := c
    path := path.push cur
  nodes := nodes.modify cur fun p => { p with data := p.data.push data }
  -- where the subexpressions start and end
  for i in [0:key.size] do
    let n := key.nodes[i]!
    if !Node.isVar n then
      let len := Node.len n
      let last := path[i + len]!
      if !nodes[last]!.lens.contains len then
        nodes := nodes.modify last fun p => { p with lens := p.lens.push len }
        let first := path[i]!
        nodes := nodes.modify first fun p => { p with ends := p.ends.push last }
  return { nodes, size := ix.size + 1 }

/-- `ruIndexSubexpr`: the subexpression that starts at node `first` of the trie and ends
at node `last`. -/
def subexpr (ix : Index α) (first last : Nat) : Exp := Id.run do
  -- the branch, from `last` up to `first`
  let mut branch : Array Nat := #[]
  let mut cur := last
  while cur != first do
    branch := branch.push cur
    cur := ix.nodes[cur]!.parent
  branch := (branch.push first).reverse
  -- the length of the application at each place of the branch
  let mut out : Array Nat := branch.map fun c => ix.nodes[c]!.key
  for i in [0:branch.size] do
    for len in ix.nodes[branch[i]!]!.lens do
      if len ≤ i && len > 0 then
        let start := i - len
        out := out.set! start (Node.setLen out[start]! len)
  return ⟨out⟩

/-- `RuUnified`: a stored datum, the unifier of its expression with the given one, and
the given expression under that unifier. -/
structure Unified (α : Type) where
  sub : Subst
  data : α
  expr : Exp

mutual

/-- `ruDoUnifyIndex`: node `i` of `e` against the children of node `at_` of the trie. -/
partial def unifyAt (ix : Index α) (e : Exp) (i at_ : Nat) (sub : Subst)
    (acc : Array (Unified α)) : Array (Unified α) := Id.run do
  if i ≥ e.size then return acc
  let n := e.nodes[i]!
  let here := ix.nodes[at_]!
  let mut acc := acc
  if !Node.isVar n then
    -- the same term in the trie
    if let some c := ix.findRule at_ (Node.appId n) then
      acc := unifyNode ix e i c sub acc
    -- a variable of the trie takes the whole subexpression
    if !here.vars.isEmpty then
      let ex := e.sub i
      for c in here.vars do
        acc := bindVar ix e (i + Node.len n) c ix.nodes[c]!.key ex sub acc
  else
    -- the variable of `e` takes every subexpression that starts here
    for c in here.rules do
      for last in ix.nodes[c]!.ends do
        acc := bindVar ix e i last n (ix.subexpr c last) sub acc
    for c in here.vars do
      acc := bindVar ix e i c ix.nodes[c]!.key (Exp.ofVar n) sub acc
  return acc

/-- `unify_var` and `unify_step` of `ruDoUnifyIndex`: binds `v` to `ex`, or unifies `ex`
with what `v` is bound to, and goes on after position `j`, from node `at_` of the trie. -/
partial def bindVar (ix : Index α) (e : Exp) (j at_ : Nat) (v : Nat) (ex : Exp) (sub : Subst)
    (acc : Array (Unified α)) : Array (Unified α) :=
  -- which of the two is bound, if `ex` is a variable of a more general type
  let (v, ex, ok) :=
    if Ty.fits (Node.ty v) ex.ty then (v, ex, true)
    else if ex.isVar && Ty.fits ex.ty (Node.ty v) then (ex.nodes[0]!, Exp.ofVar v, true)
    else (v, ex, false)
  if !ok then acc
  else
    let next :=
      match sub.lookup v with
      | some ex1 => unifyExps #[ex1, ex] sub
      | none => sub.add v ex
    match next with
    | some s => unifyNode ix e j at_ s acc
    | none => acc

/-- `ruDoUnifyIndexNode`: position `i` of `e` has been matched and led to node `at_`. -/
partial def unifyNode (ix : Index α) (e : Exp) (i at_ : Nat) (sub : Subst)
    (acc : Array (Unified α)) : Array (Unified α) :=
  if i + 1 == e.size then
    let instance_ := sub.apply e
    ix.nodes[at_]!.data.foldl (init := acc) fun acc d => acc.push ⟨sub, d, instance_⟩
  else unifyAt ix e (i + 1) at_ sub acc

end

/-- `ruUnifyIndex`: everything stored under an expression that unifies with `e`, under
an extension of `sub`. -/
def unify (ix : Index α) (e : Exp) (sub : Subst := {}) : Array (Unified α) :=
  unifyAt ix e 0 0 sub #[]

/-- `ruIndexValues` -/
def values (ix : Index α) : Array α :=
  ix.nodes.foldl (init := #[]) fun acc n => acc ++ n.data

end Index

end Whitehead.Prove
