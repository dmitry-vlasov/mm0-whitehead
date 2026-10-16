/-
The proof stack machine of the MMB format: `docs/MMB-NOTES.md` section 6, with the
decisions of its section 9. The rules follow the formal semantics (`mm0-lean/mm0/mm0b.lean`
for the machine, `examples/mm0.mm0` for what a valid proof is); the comments name the
rule each function implements.

The checking logic is kept plain. Speed comes from the representation:

- commands are read from the bytes of the file, never materialized;
- expressions live in one flat `Array Nat`, the *store*, which is emptied for every
  statement. A node is identified by the index of its first slot, and two expressions
  are the same only if they are the same node. That is the equality of the format; there
  is no hashing and no structural comparison;
- stack and heap elements are single numbers, so all arrays hold unboxed values and a
  command allocates nothing but array slots;
- the loop over the commands of a proof (`run`) carries the store, the stack, the heap
  and the unify stack and heap as separate variables, each with a single owner, so that
  a push or a pop is done in
  place. The functions it calls read these arrays and return a number, or take one array
  and return it. The rest of the state is the record `Machine`, which the loop touches
  only for the rare commands (`stepOther`).

Layout of a node at index `e`: `store[e]` is its type word, `store[e+1]` is `0` for a
variable and `t + 1` for an application of term `t`, followed by the argument nodes.
-/
import Whitehead.Mmb.Reader

namespace Whitehead.Verify

open Whitehead.Mmb

/-! The type word of a node: bits 0–54 the set of bound variables it depends on, bits
55–61 its sort, bit 62 set for a bound variable. It always fits an unboxed `Nat`.

The words are stored as `Nat` (an `Array Nat` of small numbers holds them unboxed) and
taken apart as `UInt64`. A `Nat` literal of 2^32 or more inside a function is compiled
to a call that parses its decimal digits each time it runs, which took a quarter of the
run time when the masks below were written as `Nat` literals; `UInt64` literals are
machine constants. -/
namespace Ty

/-- The dependency bits. -/
@[inline] def deps (ty : Nat) : Nat := (ty.toUInt64 &&& 0x7FFFFFFFFFFFFF).toNat
@[inline] def sort (ty : Nat) : Nat := ((ty.toUInt64 >>> 55) &&& 0x7F).toNat
@[inline] def bound (ty : Nat) : Bool := (ty.toUInt64 >>> 62) != 0

/-- The dependency sets `a` and `b` have a common element. -/
@[inline] def meets (a b : Nat) : Bool := (a.toUInt64 &&& b.toUInt64) != 0

/-- The dependency set `a` without the elements of `b`. -/
@[inline] def minus (a b : Nat) : Nat := (a.toUInt64 &&& ~~~b.toUInt64).toNat

@[inline] def union (a b : Nat) : Nat := (a.toUInt64 ||| b.toUInt64).toNat

/-- Is bit `j` set in the dependency set `a`? -/
@[inline] def hasBit (a j : Nat) : Bool := ((a.toUInt64 >>> j.toUInt64) &&& 1) != 0

def mk (sort : Nat) (bound : Bool) (deps : Nat) : Nat :=
  (deps.toUInt64 ||| (sort.toUInt64 <<< 55) ||| (if bound then (1 : UInt64) <<< 62 else 0)).toNat

/-- The type word of a binder of the file. -/
def ofArg (a : Arg) : Nat :=
  mk a.sort a.bound a.deps.toNat

/-- Do the two type words have the same sort? -/
@[inline] def sameSort (a b : Nat) : Bool := ((a.toUInt64 ^^^ b.toUInt64) >>> 55) &&& 0x7F == 0

/-- The dependency set of the bound variable number `k`. -/
@[inline] def bit (k : Nat) : Nat := ((1 : UInt64) <<< k.toUInt64).toNat

/-- The type word of a term node: the result word of the term, with these dependencies. -/
@[inline] def withDeps (ret deps : Nat) : Nat := (ret.toUInt64 ||| deps.toUInt64).toNat

end Ty

/-! Stack and heap elements as numbers: the kind in the low two bits, then one or two
node indices of 30 bits each. -/
namespace El

@[inline] def expr (e : Nat) : Nat := (e.toUInt64 <<< 2).toNat
/-- `⊢ e` -/
@[inline] def proof (e : Nat) : Nat := ((e.toUInt64 <<< 2) ||| 1).toNat
/-- A conversion `e1 = e2`. -/
@[inline] def conv (e1 e2 : Nat) : Nat := ((e1.toUInt64 <<< (2 : UInt64)) ||| (2 : UInt64) ||| (e2.toUInt64 <<< (32 : UInt64))).toNat
/-- An obligation `e1 =?= e2`. -/
@[inline] def coconv (e1 e2 : Nat) : Nat := ((e1.toUInt64 <<< (2 : UInt64)) ||| (3 : UInt64) ||| (e2.toUInt64 <<< (32 : UInt64))).toNat

/-- The kind of an element: 0 an expression, 1 a proof, 2 a conversion, 3 an obligation. -/
@[inline] def tag (el : Nat) : UInt64 := el.toUInt64 &&& 3
@[inline] def fst (el : Nat) : Nat := ((el.toUInt64 >>> 2) &&& 0x3FFFFFFF).toNat
@[inline] def snd (el : Nat) : Nat := (el.toUInt64 >>> 32).toNat

end El

/-- A node index must fit the 30 bits of a stack element. -/
def maxStore : Nat := 0x3FFFFFFF

/-- What the machine needs from the file, laid out for fast access. Binder types are in
the encoding of `Ty`. -/
structure Ctx where
  /-- The file: the unify streams are read from here. -/
  bytes : ByteArray
  /-- Where proof commands are read from: the file, or a proof body that is checked on
  its own (`checkBody`). -/
  proof : ByteArray
  /-- Per sort: its modifier bits (pure 1, strict 2, provable 4, free 8). -/
  sortMods : Array Nat
  termNargs : Array Nat
  /-- Per term: where its binder types start in `argTys`. -/
  termArgs : Array Nat
  /-- Per term: the type word of a result with no dependencies. -/
  termRet : Array Nat
  /-- Per term: the dependency bits of its return type, over its bound arguments. -/
  termRetDeps : Array Nat
  /-- Per term: where its unify stream starts, `0` if it is not a def. -/
  termUnify : Array Nat
  thmNargs : Array Nat
  thmArgs : Array Nat
  thmUnify : Array Nat
  argTys : Array Nat

def Ctx.ofFile (f : MmbFile) : Ctx := Id.run do
  let mut argTys : Array Nat := #[]
  let mut termNargs := Array.mkEmpty f.terms.size
  let mut termArgs := Array.mkEmpty f.terms.size
  let mut termRet := Array.mkEmpty f.terms.size
  let mut termRetDeps := Array.mkEmpty f.terms.size
  let mut termUnify := Array.mkEmpty f.terms.size
  for i in [0:f.terms.size] do
    let t := f.terms[i]!
    termNargs := termNargs.push t.numArgs
    termArgs := termArgs.push argTys.size
    for a in f.termArgs i do
      argTys := argTys.push (Ty.ofArg a)
    let ret := f.termRet i
    termRet := termRet.push (Ty.mk ret.sort false 0)
    termRetDeps := termRetDeps.push ret.deps.toNat
    termUnify := termUnify.push (if t.isDef then f.termUnifyPos i else 0)
  let mut thmNargs := Array.mkEmpty f.thms.size
  let mut thmArgs := Array.mkEmpty f.thms.size
  let mut thmUnify := Array.mkEmpty f.thms.size
  for i in [0:f.thms.size] do
    thmNargs := thmNargs.push f.thms[i]!.numArgs
    thmArgs := thmArgs.push argTys.size
    for a in f.thmArgs i do
      argTys := argTys.push (Ty.ofArg a)
    thmUnify := thmUnify.push (f.thmUnifyPos i)
  return { bytes := f.bytes, proof := f.bytes, sortMods := f.sorts.map (·.raw.toNat), termNargs, termArgs, termRet,
           termRetDeps, termUnify, thmNargs, thmArgs, thmUnify, argTys }

/-- The state of the machine. -/
structure Machine where
  store : Array Nat := #[]
  stack : Array Nat := #[]
  heap : Array Nat := #[]
  /-- The hypotheses declared by `Hyp`, each as the element `⊢ h`. -/
  hyps : Array Nat := #[]
  /-- The unify stack. -/
  ustack : Array Nat := #[]
  /-- The unify heap: `2 * node`, plus `1` for an entry made by `UTermSave`. -/
  uheap : Array Nat := #[]
  /-- The number of bound variables so far; the next dummy gets this bit. -/
  nextBv : Nat := 0
  /-- How many sorts, terms and theorems have been declared: only those may be used. -/
  numSorts : Nat := 0
  numTerms : Nat := 0
  numThms : Nat := 0
  /-- The offset of the statement or command being checked, for error messages. -/
  pos : Nat := 0

/-- An error is a message; its position is `Machine.pos` at the time. -/
abbrev M := EStateM String Machine

@[inline] def fail {α : Type} (msg : String) : M α :=
  throw msg

@[inline] def push (el : Nat) : M Unit :=
  modify fun m => { m with stack := m.stack.push el }

@[inline] def pushHeap (el : Nat) : M Unit :=
  modify fun m => { m with heap := m.heap.push el }

@[inline] def pop : M Nat := fun m =>
  if m.stack.size == 0 then .error "stack underflow" m
  else .ok m.stack.back! { m with stack := m.stack.pop }

/-- Pops an expression and returns its node. -/
@[inline] def popExpr : M Nat := do
  let el ← pop
  if El.tag el != 0 then fail "expected an expression on the stack"
  return el >>> 2

/-- Pops an obligation `e1 =?= e2` and returns it as it is encoded. -/
@[inline] def popCoconv : M Nat := do
  let el ← pop
  if El.tag el != 3 then fail "expected a conversion obligation `e1 =?= e2` on the stack"
  return el

/-- A new variable node with the given type word. -/
@[inline] def allocVar (ty : Nat) : M Nat := fun m =>
  let e := m.store.size
  if e ≥ maxStore then .error "this proof needs more than 2^30 store slots" m
  else .ok e { m with store := (m.store.push ty).push 0 }

/-! ### Reading commands -/

@[inline] def cmdSize (first : UInt8) : Nat :=
  let w := first >>> 6
  if w == 0 then 1 else if w == 1 then 2 else if w == 2 then 3 else 5

/-- The data of the command at `pos`, whose first byte is `first`. The command must lie
inside the file. -/
@[inline] def cmdData (b : ByteArray) (pos : Nat) (first : UInt8) : Nat :=
  let w := first >>> 6
  if w == 0 then 0
  else if w == 1 then (b.get! (pos + 1)).toNat
  else if w == 2 then Reader.u16 b (pos + 1)
  else Reader.u32 b (pos + 1)

/-! ### Unification (section 6, "Unify commands") -/

inductive UMode where
  /-- Applying a theorem: `UHyp` takes a subproof from the main stack. -/
  | thm
  /-- Unfolding a definition, or checking a def against its own stream. -/
  | defn
  /-- Checking an axiom or theorem against its own stream: `UHyp` takes a declared
  hypothesis. -/
  | thmEnd
  deriving BEq

/-- What a unification leaves: the two arrays it worked on, to be used again, and how it
went. -/
structure UResult where
  ustack : Array Nat
  uheap : Array Nat
  /-- How many hypotheses are still to be matched. -/
  hyps : Nat
  /-- Empty if the unification succeeded. -/
  error : String
  deriving Inhabited

/-- Is `d` disjoint from the dependencies of every entry of the unify heap that was not
made by `UTermSave`: the arguments and the earlier dummies? -/
partial def dummyIsFresh (store uheap : Array Nat) (d : Nat) (i : Nat) : Bool :=
  if i ≥ uheap.size then true
  else
    let h := uheap[i]!
    if h &&& 1 == 0 && Ty.meets store[h >>> 1]! d then false
    else dummyIsFresh store uheap d (i + 1)

/-- Pushes the arguments of the application node `p` on the unify stack, the first one
on top. -/
partial def pushArgs (store : Array Nat) (p n : Nat) (ustack : Array Nat) : Array Nat :=
  if n == 0 then ustack
  else pushArgs store p (n - 1) (ustack.push store[p + 1 + n]!)

/-- Runs the unify stream at `pos`. The unify stack holds the target and the unify heap
the substitution. The hypotheses that `UHyp` takes are the first `k` elements of `hs`,
the last one first: the main stack when a theorem is applied, the declared hypotheses
when a statement is checked against its own stream. -/
partial def unify (c : Ctx) (mode : UMode) (store hs : Array Nat) (pos k : Nat)
    (ustack uheap : Array Nat) : UResult :=
  let b := c.bytes
  if pos ≥ b.size then ⟨ustack, uheap, k, "unify: the stream runs past the end of the file"⟩
  else
    let first := b.get! pos
    let next := pos + cmdSize first
    if next > b.size then ⟨ustack, uheap, k, "unify: the stream runs past the end of the file"⟩
    else
      let data := cmdData b pos first
      let op := first &&& 0x3F
      if op == 0x32 then
        -- URef i: the top of the unify stack is heap entry i, the same node
        if data ≥ uheap.size then
          ⟨ustack, uheap, k, s!"unify: reference to heap entry {data}, which does not exist"⟩
        else if ustack.size == 0 then ⟨ustack, uheap, k, "unify: stack underflow"⟩
        else if ustack.back! != uheap[data]! >>> 1 then
          ⟨ustack, uheap, k, s!"unify failure at 0x{hex pos}: the expression is not the one substituted for heap entry {data}"⟩
        else unify c mode store hs next k ustack.pop uheap
      else if op == 0x30 || op == 0x31 then
        -- UTerm t: the top is an application of t; replace it by its arguments
        if ustack.size == 0 then ⟨ustack, uheap, k, "unify: stack underflow"⟩
        else
          let p := ustack.back!
          if store[p + 1]! != data + 1 then
            ⟨ustack, uheap, k, s!"unify failure at 0x{hex pos}: the expression is not an application of term {data}"⟩
          else
            let ustack := pushArgs store p c.termNargs[data]! ustack.pop
            unify c mode store hs next k ustack (if op == 0x31 then uheap.push (2 * p + 1) else uheap)
      else if op == 0x33 then
        -- UDummy s: the top is a bound variable of sort s, new with respect to the
        -- arguments and the earlier dummies
        if mode != .defn then ⟨ustack, uheap, k, "unify: UDummy outside a definition"⟩
        else if ustack.size == 0 then ⟨ustack, uheap, k, "unify: stack underflow"⟩
        else
          let p := ustack.back!
          let ty := store[p]!
          if store[p + 1]! != 0 || !Ty.bound ty || Ty.sort ty != data then
            ⟨ustack, uheap, k, s!"unify failure at 0x{hex pos}: a bound variable of sort {data} is expected for a dummy"⟩
          else if !dummyIsFresh store uheap (Ty.deps ty) 0 then
            ⟨ustack, uheap, k, s!"unify failure at 0x{hex pos}: the variable taken for a dummy also occurs in the arguments or is another dummy"⟩
          else unify c mode store hs next k ustack.pop (uheap.push (2 * p))
      else if op == 0x36 then
        -- UHyp: the next hypothesis becomes the target
        match mode with
        | .defn => ⟨ustack, uheap, k, "unify: UHyp in a definition"⟩
        | .thm =>
          if k == 0 then ⟨ustack, uheap, k, "unify: a subproof is missing on the stack"⟩
          else
            let el := hs[k - 1]!
            if El.tag el != 1 then ⟨ustack, uheap, k, "unify: expected the proof of a hypothesis on the stack"⟩
            else unify c mode store hs next (k - 1) (ustack.push (el >>> 2)) uheap
        | .thmEnd =>
          if ustack.size != 0 then
            ⟨ustack, uheap, k, "unify: the statement is not matched completely before the next hypothesis"⟩
          else if k == 0 then
            ⟨ustack, uheap, k, "unify failure: the statement has more hypotheses than the proof declares"⟩
          else unify c mode store hs next (k - 1) (ustack.push (hs[k - 1]! >>> 2)) uheap
      else if op == 0 then
        if ustack.size != 0 then
          ⟨ustack, uheap, k, "unify: the stream ends before the expression is matched completely"⟩
        else if mode == .thmEnd && k != 0 then
          ⟨ustack, uheap, k, "unify failure: the proof declares more hypotheses than the statement has"⟩
        else ⟨ustack, uheap, k, ""⟩
      else ⟨ustack, uheap, k, s!"unify: unknown command 0x{hex op.toNat}"⟩

/-- Unifies `target` with the stream at `pos`, the unify heap of the machine being the
substitution. Hypotheses are the declared ones. -/
def unifyWith (c : Ctx) (mode : UMode) (pos target : Nat) : M Unit := fun m =>
  let ustack := m.ustack
  let uheap := m.uheap
  let m := { m with ustack := #[], uheap := #[] }
  match unify c mode m.store m.hyps pos m.hyps.size ((ustack.shrink 0).push target) uheap with
  | ⟨ustack, uheap, _, error⟩ =>
    let m := { m with ustack, uheap }
    if error.isEmpty then .ok () m else .error error m

/-! ### The arguments of `Term` and `Thm`

The `n` arguments are the stack elements from `base` on; their binders are the type
words of `Ctx.argTys` from `off` on. Bit `k` of the dependencies of a binder stands for
the `k`-th bound binder of the same term or theorem. -/

/-- The union of the variables of the arguments given for the bound binders before
binder `i`: those that `mask` selects if `sel`, those that it does not select otherwise.
`j` runs over the binders and `k` counts the bound ones. -/
partial def boundDeps (c : Ctx) (store stack : Array Nat) (off base i mask : Nat) (sel : Bool)
    (j k acc : Nat) : Nat :=
  if j == i then acc
  else if Ty.bound c.argTys[off + j]! then
    let acc :=
      if Ty.hasBit mask k == sel then Ty.union acc (Ty.deps store[stack[base + j]! >>> 2]!) else acc
    boundDeps c store stack off base i mask sel (j + 1) (k + 1) acc
  else boundDeps c store stack off base i mask sel (j + 1) k acc

/-- Checks the arguments against their binders. The result is `0` if they all fit, and
`kind + 8 * i` for the first argument `i` that does not:

1. it is not an expression;
2. its sort is not the sort of the binder;
3. the binder is a bound variable and the argument is not one;

and, for the substitution of a theorem (`dv`), the disjoint variable conditions
(`safe_subst` in `mm0.lean`):

4. the variable given for a bound binder occurs in an earlier argument;
5. the expression given for a regular binder contains a variable given for a bound
   binder that it is not declared to depend on.

`seen` is the union of the dependencies of the arguments before `i`. -/
partial def argsFault (c : Ctx) (dv : Bool) (store stack : Array Nat) (off base n i seen : Nat) : Nat :=
  if i == n then 0
  else
    let el := stack[base + i]!
    if El.tag el != 0 then 1 + 8 * i
    else
      let ety := store[el >>> 2]!
      let target := c.argTys[off + i]!
      if !Ty.sameSort ety target then 2 + 8 * i
      else if Ty.bound target && !Ty.bound ety then 3 + 8 * i
      else if !dv then argsFault c dv store stack off base n (i + 1) seen
      else
        let d := Ty.deps ety
        if Ty.bound target then
          if Ty.meets d seen then 4 + 8 * i
          else argsFault c dv store stack off base n (i + 1) (Ty.union seen d)
        else if Ty.meets d (boundDeps c store stack off base i (Ty.deps target) false 0 0 0) then 5 + 8 * i
        else argsFault c dv store stack off base n (i + 1) (Ty.union seen d)

/-- The message for a result of `argsFault` that is not `0`. -/
def faultMessage (c : Ctx) (cmd : String) (store stack : Array Nat) (off base fault : Nat) : String :=
  let i := fault / 8
  match fault % 8 with
  | 1 => s!"{cmd}: argument {i} is not an expression"
  | 2 => s!"{cmd}: argument {i} has sort {Ty.sort store[stack[base + i]! >>> 2]!}, the binder has sort {Ty.sort c.argTys[off + i]!}"
  | 3 => s!"{cmd}: argument {i} must be a bound variable"
  | 4 => s!"disjoint variable violation: the variable given for the bound argument {i} occurs in an earlier argument"
  | _ => s!"disjoint variable violation: argument {i} contains a bound variable it is not declared to depend on"

/-- The variables of the arguments: the dependencies of a term in a theorem (`HasVar` in
`mm0.mm0`). -/
partial def argsVars (store stack : Array Nat) (base n i acc : Nat) : Nat :=
  if i == n then acc
  else argsVars store stack base n (i + 1) (Ty.union acc (Ty.deps store[stack[base + i]! >>> 2]!))

/-- The free variables of the arguments: the dependencies of a term in a definition
(`Free` in `mm0.mm0`), but for the bound arguments that its return type depends on. A
bound argument contributes nothing here, and a regular argument contributes its own
variables minus the bound arguments its binder is declared to depend on. -/
partial def argsFree (c : Ctx) (store stack : Array Nat) (off base n i acc : Nat) : Nat :=
  if i == n then acc
  else
    let target := c.argTys[off + i]!
    if Ty.bound target then argsFree c store stack off base n (i + 1) acc
    else
      let d := Ty.deps store[stack[base + i]! >>> 2]!
      let bound := boundDeps c store stack off base i (Ty.deps target) true 0 0 0
      argsFree c store stack off base n (i + 1) (Ty.union acc (Ty.minus d bound))

/-- Appends the argument nodes to the store: the arguments of a new application node. -/
partial def argsToStore (stack : Array Nat) (base n i : Nat) (store : Array Nat) : Array Nat :=
  if i == n then store
  else argsToStore stack base n (i + 1) (store.push (stack[base + i]! >>> 2))

/-- Appends the argument nodes to the unify heap: the substitution of a theorem. -/
partial def argsToUheap (stack : Array Nat) (base n i : Nat) (uheap : Array Nat) : Array Nat :=
  if i == n then uheap
  else argsToUheap stack base n (i + 1) (uheap.push (2 * (stack[base + i]! >>> 2)))

/-! ### Proof commands (section 6, "Proof commands") -/

/-- Pushes `a_n =?= b_n, ..., a_1 =?= b_1` for the arguments of two applications. -/
partial def pushCong (e1 e2 n : Nat) : M Unit := fun m =>
  if n == 0 then .ok () m
  else
    pushCong e1 e2 (n - 1)
      { m with stack := m.stack.push (El.coconv m.store[e1 + 1 + n]! m.store[e2 + 1 + n]!) }

/-- Loads the arguments of the application node `p` as the unify heap. -/
partial def loadUheap (p n i : Nat) (m : Machine) : Machine :=
  if i == n then m
  else loadUheap p n (i + 1) { m with uheap := m.uheap.push (2 * m.store[p + 2 + i]!) }

/-- The commands other than `Term`, `Thm` and `Ref`. They are rare, and written on the
whole machine. -/
def stepOther (c : Ctx) (isDef : Bool) (op : UInt8) (data : Nat) : M Unit := do
  if op == 0x13 then
    -- Dummy s: a new bound variable, on the stack and on the heap
    let m ← get
    if data ≥ m.numSorts then fail s!"Dummy: sort {data} is not declared before this statement"
    -- A type word holds 7 bits of sort, as a binder does: a dummy of a sort ≥ 128 could
    -- be the argument of no term or theorem, and would be taken for sort `data % 128`
    -- (MMB-NOTES section 9, point 22).
    if data ≥ 128 then fail s!"Dummy: sort {data} is the sort of no binder (sorts in types are 7 bits)"
    if c.sortMods[data]! &&& 10 != 0 then fail s!"Dummy: sort {data} is strict or free"
    if m.nextBv ≥ 55 then fail "more than 55 bound variables"
    let e ← allocVar (Ty.mk data true (Ty.bit m.nextBv))
    modify fun m => { m with nextBv := m.nextBv + 1 }
    push (El.expr e)
    pushHeap (El.expr e)
  else if op == 0x16 then
    -- Hyp: `HS; H; S, e --> HS, e; H, ⊢ e; S`
    if isDef then fail "Hyp in a definition"
    let e ← popExpr
    let m ← get
    if c.sortMods[Ty.sort m.store[e]!]! &&& 4 == 0 then fail "Hyp: the hypothesis does not have a provable sort"
    modify fun m => { m with hyps := m.hyps.push (El.proof e) }
    pushHeap (El.proof e)
  else if op == 0x17 then
    -- Conv: `S, e1, ⊢ e2 --> S, ⊢ e1, e1 =?= e2`
    let el ← pop
    if El.tag el != 1 then fail "Conv: expected a proof on the stack"
    let e1 ← popExpr
    push (El.proof e1)
    push (El.coconv e1 (el >>> 2))
  else if op == 0x18 then
    -- Refl: `S, e =?= e --> S`, the two sides being the same node
    let el ← popCoconv
    if El.fst el != El.snd el then fail "Refl: the two sides are not the same expression"
  else if op == 0x19 then
    -- Symm: `S, e1 =?= e2 --> S, e2 =?= e1`
    let el ← popCoconv
    push (El.coconv (El.snd el) (El.fst el))
  else if op == 0x1A then
    -- Cong: `S, (t a1 ... an) =?= (t b1 ... bn) --> S, an =?= bn, ..., a1 =?= b1`
    let el ← popCoconv
    let m ← get
    let head := m.store[El.fst el + 1]!
    if head == 0 || head != m.store[El.snd el + 1]! then
      fail "Cong: the two sides are not applications of the same term"
    pushCong (El.fst el) (El.snd el) c.termNargs[head - 1]!
  else if op == 0x1B then
    -- Unfold: `S, (t e1 ... en) =?= e', e --> S, e =?= e'` if `t e1 ... en` unfolds to `e`
    let e ← popExpr
    let el ← popCoconv
    let m ← get
    let p := El.fst el
    let head := m.store[p + 1]!
    if head == 0 then fail "Unfold: the left side is not an application"
    let upos := c.termUnify[head - 1]!
    if upos == 0 then fail s!"Unfold: term {head - 1} is not a definition"
    modify fun m => loadUheap p c.termNargs[head - 1]! 0 { m with uheap := m.uheap.shrink 0 }
    unifyWith c .defn upos e
    push (El.coconv e (El.snd el))
  else if op == 0x1C then
    -- ConvCut: `S, e1 =?= e2 --> S, e1 = e2, e1 =?= e2`
    let el ← popCoconv
    push (el - 1)
    push el
  else if op == 0x1E then
    -- ConvSave: `H; S, e1 = e2 --> H, e1 = e2; S`
    let el ← pop
    if El.tag el != 2 then fail "ConvSave: expected a conversion `e1 = e2` on the stack"
    pushHeap el
  else if op == 0x1F then
    -- Save: `H; S, s --> H, s; S, s`
    let m ← get
    if m.stack.size == 0 then fail "stack underflow"
    let el := m.stack.back!
    if El.tag el == 3 then fail "Save: an obligation `e1 =?= e2` cannot be saved"
    pushHeap el
  else if op == 0x20 then
    fail "Sorry: this proof is not finished"
  else
    fail s!"unknown proof command 0x{hex op.toNat}"

/-- The machine with the arrays of the loop put back into it, at the command at `pos`. -/
@[inline] def Machine.put (m : Machine) (pos : Nat) (store stack heap ustack uheap : Array Nat) : Machine :=
  { m with store, stack, heap, ustack, uheap, pos }

/-- Leaves the loop with an error at the command at `pos`. -/
@[noinline] def halt (msg : String) (m : Machine) (pos : Nat) (store stack heap ustack uheap : Array Nat) :
    EStateM.Result String Machine Unit :=
  .error msg (m.put pos store stack heap ustack uheap)

mutual

/-- Runs the proof commands in `[pos, stop)`; the last byte of the range is the `END`. -/
partial def runProof (c : Ctx) (isDef : Bool) (pos stop : Nat) : M Unit := fun m =>
  -- the arrays are taken out of the machine, which must not keep a second reference
  let store := m.store
  let stack := m.stack
  let heap := m.heap
  let ustack := m.ustack
  let uheap := m.uheap
  run c isDef stop pos store stack heap ustack uheap
    { m with store := #[], stack := #[], heap := #[], ustack := #[], uheap := #[] }

/-- The loop of `runProof`: the command at `pos`, then the rest. `m` is the machine
without the five arrays. -/
partial def run (c : Ctx) (isDef : Bool) (stop pos : Nat) (store stack heap ustack uheap : Array Nat)
    (m : Machine) : EStateM.Result String Machine Unit :=
  if pos ≥ stop then halt "the proof does not end with END" m pos store stack heap ustack uheap
  else
    let b := c.proof
    let first := b.get! pos
    let next := pos + cmdSize first
    let op := first &&& 0x3F
    if op == 0 then
      if pos + 1 == stop then .ok () (m.put pos store stack heap ustack uheap)
      else halt "END before the end of the statement's proof" m pos store stack heap ustack uheap
    else if next > stop then
      halt "the proof does not end with END: this command crosses its end" m pos store stack heap ustack uheap
    else
      let data := cmdData b pos first
      if op == 0x12 then
        -- Ref i: push heap entry `i`; a saved conversion `e1 = e2` instead discharges the
        -- obligation `e1 =?= e2` on top of the stack
        if data ≥ heap.size then
          halt s!"Ref: heap entry {data} does not exist" m pos store stack heap ustack uheap
        else
          let el := heap[data]!
          if El.tag el != 2 then run c isDef stop next store (stack.push el) heap ustack uheap m
          else if stack.size == 0 then halt "stack underflow" m pos store stack heap ustack uheap
          else if stack.back! != el + 1 then
            halt "Ref: the saved conversion is not the obligation on the stack" m pos store stack heap ustack uheap
          else run c isDef stop next store stack.pop heap ustack uheap m
      else if op == 0x10 || op == 0x11 then
        -- Term t: `S, e1, ..., en --> S, (t e1 ... en)`; with save, also onto the heap
        if data ≥ m.numTerms then
          halt s!"Term: term {data} is not declared before this statement" m pos store stack heap ustack uheap
        else
          let n := c.termNargs[data]!
          if stack.size < n then halt "stack underflow" m pos store stack heap ustack uheap
          else
            let base := stack.size - n
            let off := c.termArgs[data]!
            let fault := argsFault c false store stack off base n 0 0
            let node := store.size
            if fault != 0 then
              halt (faultMessage c "Term" store stack off base fault) m pos store stack heap ustack uheap
            else if node ≥ maxStore then
              halt "this proof needs more than 2^30 store slots" m pos store stack heap ustack uheap
            else
              -- in a definition, the bound arguments that the return type depends on are free
              let deps :=
                if isDef then
                  boundDeps c store stack off base n c.termRetDeps[data]! true 0 0
                    (argsFree c store stack off base n 0 0)
                else argsVars store stack base n 0 0
              let store := (store.push (Ty.withDeps c.termRet[data]! deps)).push (data + 1)
              let store := argsToStore stack base n 0 store
              let el := El.expr node
              let stack := (stack.shrink base).push el
              run c isDef stop next store stack (if op == 0x11 then heap.push el else heap) ustack uheap m
      else if op == 0x14 || op == 0x15 then
        -- Thm T: `S, ⊢ h1, ..., ⊢ hm, e1, ..., en, e --> S, ⊢ e`; with save, also onto the heap
        if isDef then halt "Thm in a definition" m pos store stack heap ustack uheap
        else if data ≥ m.numThms then
          halt s!"Thm: theorem {data} is not declared before this statement" m pos store stack heap ustack uheap
        else if stack.size == 0 then halt "stack underflow" m pos store stack heap ustack uheap
        else
          let top := stack.back!
          let n := c.thmNargs[data]!
          if El.tag top != 0 then halt "expected an expression on the stack" m pos store stack heap ustack uheap
          else if stack.size - 1 < n then halt "stack underflow" m pos store stack heap ustack uheap
          else
            let base := stack.size - 1 - n
            let off := c.thmArgs[data]!
            let fault := argsFault c true store stack off base n 0 0
            if fault != 0 then
              halt (faultMessage c "Thm" store stack off base fault) m pos store stack heap ustack uheap
            else
              -- the substitution, then the conclusion and the hypotheses against the
              -- statement of the theorem; the subproofs are below the arguments
              let e := top >>> 2
              let uheap := argsToUheap stack base n 0 (uheap.shrink 0)
              match unify c .thm store stack c.thmUnify[data]! base ((ustack.shrink 0).push e) uheap with
              | ⟨ustack, uheap, rest, error⟩ =>
                if !error.isEmpty then halt error m pos store stack heap ustack uheap
                else
                  let el := El.proof e
                  let stack := (stack.shrink rest).push el
                  run c isDef stop next store stack (if op == 0x15 then heap.push el else heap) ustack uheap m
      else
        match stepOther c isDef op data (m.put pos store stack heap ustack uheap) with
        | .ok () m => runProof c isDef next stop m
        | .error e m => .error e m

end

end Whitehead.Verify
