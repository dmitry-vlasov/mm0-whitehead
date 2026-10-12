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
- everything stored has a *rank*, and a lookup can be limited to the ranks below a
  bound; a node knows the smallest rank stored under it, so the walk leaves out the
  branches that have nothing below the bound. The rank of an assertion is its place in
  the file: a theorem may use only what is declared before it. Russell builds an index
  for each theorem to be proved from the assertions that precede it
  (`ruInitTheoremAssertionsIndex`); one index with ranks gives the same answers;
- a variable is bound to an expression whose type fits it, and of two variables the more
  general is bound to the more special. Russell asks `ruSuperRule` here, with the two
  types in the other order than in `ruAdd2Subst1`.
-/
import Whitehead.Prove.Unify

namespace Whitehead.Prove

/-- The rank of a node under which nothing is stored yet: more than any real rank. It is
below 2^32 on purpose: a `Nat` literal from 2^32 on is parsed from its digits each time
it is used (see the note in `Verify/Machine.lean`), also when it is written as a
`UInt64` and converted, and this one is used for every node of the index. -/
def noRank : Nat := 0xFFFFFFFF

/-- `RuIndexNode` -/
structure IndexNode (α : Type) where
  /-- The node of the expressions that leads here: a variable node, or an application
  with its length set to 0. -/
  key : Nat
  parent : Nat
  /-- Children that are applications, and children that are variables. -/
  rules : Array Nat := #[]
  vars : Array Nat := #[]
  /-- The nodes at which a subexpression that starts here ends; for each, the
  subexpression itself, as it was put in (`subexpr` would read it back from the trie),
  and whether it has no variable. -/
  ends : Array Nat := #[]
  endExps : Array Exp := #[]
  endClosed : Array Bool := #[]
  /-- The lengths (as in `Node.len`) of the subexpressions that end here. -/
  lens : Array Nat := #[]
  /-- What is stored for the expressions that end here, each with its rank. -/
  data : Array α := #[]
  ranks : Array Nat := #[]
  /-- The smallest rank of anything stored here or below. -/
  minRank : Nat := noRank
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

/-- `ruSetIndex`: stores `data` under the expression `key`, with a rank. -/
def insert (ix : Index α) (key : Exp) (data : α) (rank : Nat := 0) : Index α := Id.run do
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
  nodes := nodes.modify cur fun p => { p with data := p.data.push data, ranks := p.ranks.push rank }
  for c in path do
    if rank < nodes[c]!.minRank then nodes := nodes.modify c fun p => { p with minRank := rank }
  -- where the subexpressions start and end
  for i in [0:key.size] do
    let n := key.nodes[i]!
    if !Node.isVar n then
      let len := Node.len n
      let last := path[i + len]!
      if !nodes[last]!.lens.contains len then
        nodes := nodes.modify last fun p => { p with lens := p.lens.push len }
        let first := path[i]!
        let ex := key.sub i
        nodes := nodes.modify first fun p =>
          { p with ends := p.ends.push last, endExps := p.endExps.push ex, endClosed := p.endClosed.push !ex.hasVars }
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

end Index

/-- The bindings that a walk of the trie has made, the newest first. A list, so that the
branches of the walk share what they have in common and extend it without copying: a
`Subst` is a hash map, and extending one that another branch holds copies it. An image
is the subexpression of `src` at node `at_`, not copied out. The list is not idempotent
as a `Subst` is — an image may mention a variable that is bound elsewhere in the list,
and `lookup` follows the chain — and `toSubst` puts that right, once, for the candidates
that are expanded: of the candidates the walk makes, next to none are. -/
inductive Binds where
  | nil
  | cons (v : Nat) (src : Exp) (at_ : Nat) (rest : Binds)

namespace Binds

def size : Binds → Nat
  | .nil => 0
  | .cons _ _ _ rest => 1 + rest.size

/-- The image of the variable with number `vid`, as an expression and the node where the
image starts in it. -/
def lookup (bs : Binds) (vid : Nat) : Option (Exp × Nat) :=
  match bs with
  | .nil => none
  | .cons v src at_ rest => if Node.varId v == vid then some (src, at_) else rest.lookup vid

/-- Does the variable `vid` occur in the subexpression of `src` at `at_`, through the
bindings? `closed` says that the subexpression has no variable: then not. -/
partial def occurs (bs : Binds) (vid : Nat) (src : Exp) (at_ : Nat) : Bool := Id.run do
  let stop := at_ + 1 + Node.len src.nodes[at_]!
  for i in [at_:stop] do
    let n := src.nodes[i]!
    if Node.isVar n then
      if Node.varId n == vid then return true
      if let some (src', at') := bs.lookup (Node.varId n) then
        if bs.occurs vid src' at' then return true
  return false

/-- Binds the variable node `v` to the subexpression of `src` at `at_`, if the type
fits and `v` does not occur in it; nothing to do if that is `v` itself. `closed`: the
subexpression is known to have no variable. -/
def bind (bs : Binds) (v : Nat) (src : Exp) (at_ : Nat) (closed : Bool := false) : Option Binds :=
  let n := src.nodes[at_]!
  if Node.isVar n && Node.varId n == Node.varId v then some bs
  else if !Ty.fits (Node.ty v) (Node.ty n) then none
  else if !closed && bs.occurs (Node.varId v) src at_ then none
  else some (.cons v src at_ bs)

/-- The subexpressions of `a` at `i` and of `b` at `j` unified under `bs`: the same
decisions as `unifyExps` — a variable is bound to what fits it, of two variables the
more general to the more special, the first to the second when both fit. -/
partial def unify (bs : Binds) (a : Exp) (i : Nat) (b : Exp) (j : Nat) : Option Binds :=
  let na := a.nodes[i]!
  let nb := b.nodes[j]!
  if Node.isVar na then
    match bs.lookup (Node.varId na) with
    | some (src, k) => bs.unify src k b j
    | none =>
      if Node.isVar nb then
        match bs.lookup (Node.varId nb) with
        | some (src, k) => bs.unify a i src k
        | none =>
          if Node.varId na == Node.varId nb then some bs
          else if Ty.fits (Node.ty na) (Node.ty nb) then some (.cons na b j bs)
          else if Ty.fits (Node.ty nb) (Node.ty na) then some (.cons nb a i bs)
          else none
      else bs.bind na b j
  else if Node.isVar nb then
    match bs.lookup (Node.varId nb) with
    | some (src, k) => bs.unify a i src k
    | none => bs.bind nb a i
  else if Node.appId na != Node.appId nb then none
  else Id.run do
    -- the arguments in step: the same term, so the same number of them
    let stop := i + 1 + Node.len na
    let mut ka := i + 1
    let mut kb := j + 1
    let mut acc := bs
    while ka < stop do
      match acc.unify a ka b kb with
      | some acc' => acc := acc'
      | none => return none
      ka := ka + 1 + Node.len a.nodes[ka]!
      kb := kb + 1 + Node.len b.nodes[kb]!
    return some acc

/-- The bindings as a `Subst`, which is idempotent: each is added in the order it was
made, and `Subst.add` applies it through. `none` only for a cycle, which `bind` keeps
out. -/
def toSubst (bs : Binds) : Option Subst :=
  go bs (some {})
where
  go : Binds → Option Subst → Option Subst
    | .nil, acc => acc
    | .cons v src at_ rest, acc => (go rest acc).bind fun s => s.add v (src.sub at_)

/-- A `Subst` as bindings. -/
def ofSubst (s : Subst) : Binds :=
  s.map.fold (init := .nil) fun bs _ x => .cons x.var x.exp 0 bs

end Binds

namespace Index

variable {α : Type}

/-- A stored datum with the bindings that unify its expression with the given one. -/
structure RawUnified (α : Type) where
  binds : Binds
  data : α

/-- `RuUnified`: a stored datum, the unifier of its expression with the given one, and
the given expression under that unifier. -/
structure Unified (α : Type) where
  sub : Subst
  data : α
  /-- Made when it is asked for: most results are candidates whose instance nobody
  reads. -/
  instance_ : Thunk Exp

/-- The given expression under the unifier. -/
def Unified.expr {α : Type} (u : Unified α) : Exp := u.instance_.get

/-- The expression a walk is about, with what the walk asks of its subexpressions. -/
structure Walk where
  e : Exp
  /-- For each node, whether a variable is below it. -/
  open_ : Array Bool

/-- `Walk` of `e`. -/
def Walk.mk' (e : Exp) : Walk := Id.run do
  let mut open_ : Array Bool := Array.replicate e.size false
  for k in [0:e.size] do
    let i := e.size - 1 - k
    let n := e.nodes[i]!
    if Node.isVar n then open_ := open_.set! i true
    else
      let stop := i + 1 + Node.len n
      let mut j := i + 1
      while j < stop do
        if open_[j]! then
          open_ := open_.set! i true
          j := stop
        else j := j + 1 + Node.len e.nodes[j]!
  return { e, open_ }

mutual

/-- `ruDoUnifyIndex`: node `i` of `e` against the children of node `at_` of the trie. -/
partial def unifyAt (ix : Index α) (limit : Nat) (w : Walk) (i at_ : Nat) (bs : Binds)
    (acc : Array (RawUnified α)) : Array (RawUnified α) := Id.run do
  let e := w.e
  if i ≥ e.size then return acc
  let n := e.nodes[i]!
  let here := ix.nodes[at_]!
  let mut acc := acc
  if !Node.isVar n then
    -- the same term in the trie
    if let some c := ix.findRule at_ (Node.appId n) then
      if ix.nodes[c]!.minRank < limit then
        acc := unifyNode ix limit w i c bs acc
    -- a variable of the trie takes the whole subexpression
    for c in here.vars do
      if ix.nodes[c]!.minRank < limit then
        acc := bindVar ix limit w (i + Node.len n) c ix.nodes[c]!.key e i (!w.open_[i]!) bs acc
  else
    -- the variable of `e` takes every subexpression that starts here
    for c in here.rules do
      if ix.nodes[c]!.minRank < limit then
        let node := ix.nodes[c]!
        for k in [0:node.ends.size] do
          let last := node.ends[k]!
          if ix.nodes[last]!.minRank < limit then
            acc := bindVar ix limit w i last n node.endExps[k]! 0 node.endClosed[k]! bs acc
    for c in here.vars do
      if ix.nodes[c]!.minRank < limit then
        acc := bindVar ix limit w i c ix.nodes[c]!.key e i false bs acc
  return acc

/-- `unify_var` and `unify_step` of `ruDoUnifyIndex`: binds `v` to the subexpression of
`src` at `k` (`closed`: which has no variable), or unifies that with what `v` is bound
to, and goes on after position `j`, from node `at_` of the trie. -/
partial def bindVar (ix : Index α) (limit : Nat) (w : Walk) (j at_ : Nat) (v : Nat) (src : Exp) (k : Nat)
    (closed : Bool) (bs : Binds) (acc : Array (RawUnified α)) : Array (RawUnified α) :=
  -- which of the two is bound, if the image is a variable of a more general type
  let m := src.nodes[k]!
  let (v, src, k, ok) :=
    if Ty.fits (Node.ty v) (Node.ty m) then (v, src, k, true)
    else if Node.isVar m && Ty.fits (Node.ty m) (Node.ty v) then (m, Exp.ofVar v, 0, true)
    else (v, src, k, false)
  if !ok then acc
  else
    let next :=
      match bs.lookup (Node.varId v) with
      | some (src1, k1) => bs.unify src1 k1 src k
      | none => bs.bind v src k closed
    match next with
    | some bs => unifyNode ix limit w j at_ bs acc
    | none => acc

/-- `ruDoUnifyIndexNode`: position `i` of `e` has been matched and led to node `at_`. -/
partial def unifyNode (ix : Index α) (limit : Nat) (w : Walk) (i at_ : Nat) (bs : Binds)
    (acc : Array (RawUnified α)) : Array (RawUnified α) := Id.run do
  if i + 1 == w.e.size then
    let node := ix.nodes[at_]!
    return (node.data.zip node.ranks).foldl (init := acc) fun acc (d, rank) =>
      if rank < limit then acc.push ⟨bs, d⟩ else acc
  else unifyAt ix limit w (i + 1) at_ bs acc

end

/-- `ruUnifyIndex`, with the bindings as the walk made them: everything stored under an
expression that unifies with `e`; with `limit`, only what has a rank below it. -/
def unifyRaw (ix : Index α) (e : Exp) (limit : Nat := noRank) : Array (RawUnified α) :=
  unifyAt ix limit (Walk.mk' e) 0 0 .nil #[]

/-- `ruUnifyIndex`: as `unifyRaw`, each result with its unifier as a `Subst` and the
instance of `e`. -/
def unify (ix : Index α) (e : Exp) (sub : Subst := {}) (limit : Nat := noRank) : Array (Unified α) :=
  let start := if sub.size == 0 then Binds.nil else Binds.ofSubst sub
  (unifyAt ix limit (Walk.mk' e) 0 0 start #[]).filterMap fun r =>
    (r.binds.toSubst).map fun s => ⟨s, r.data, Thunk.mk fun _ => s.apply e⟩

/-- `ruIndexValues` -/
def values (ix : Index α) : Array α :=
  ix.nodes.foldl (init := #[]) fun acc n => acc ++ n.data

end Index

end Whitehead.Prove
