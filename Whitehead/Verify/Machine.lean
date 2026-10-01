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
  command allocates nothing but array slots.

Layout of a node at index `e`: `store[e]` is its type word, `store[e+1]` is `0` for a
variable and `t + 1` for an application of term `t`, followed by the argument nodes.
-/
import Whitehead.Mmb.Reader

namespace Whitehead.Verify

open Whitehead.Mmb

/-! The type word of a node: bits 0–54 the set of bound variables it depends on, bits
55–61 its sort, bit 62 set for a bound variable. It always fits an unboxed `Nat`. -/
namespace Ty

def depsMask : Nat := 0x7FFFFFFFFFFFFF

@[inline] def deps (ty : Nat) : Nat := ty &&& depsMask
@[inline] def sort (ty : Nat) : Nat := (ty >>> 55) &&& 0x7F
@[inline] def bound (ty : Nat) : Bool := (ty >>> 62) != 0

def mk (sort : Nat) (bound : Bool) (deps : Nat) : Nat :=
  deps + sort * 0x80000000000000 + (if bound then 0x4000000000000000 else 0)

/-- The type word of a binder of the file. -/
def ofArg (a : Arg) : Nat :=
  mk a.sort a.bound a.deps.toNat

end Ty

/-! Stack and heap elements as numbers: the kind in the low two bits, then one or two
node indices of 30 bits each. -/
namespace El

@[inline] def expr (e : Nat) : Nat := e * 4
/-- `⊢ e` -/
@[inline] def proof (e : Nat) : Nat := e * 4 + 1
/-- A conversion `e1 = e2`. -/
@[inline] def conv (e1 e2 : Nat) : Nat := e1 * 4 + 2 + e2 * 0x100000000
/-- An obligation `e1 =?= e2`. -/
@[inline] def coconv (e1 e2 : Nat) : Nat := e1 * 4 + 3 + e2 * 0x100000000

@[inline] def tag (el : Nat) : Nat := el &&& 3
@[inline] def fst (el : Nat) : Nat := (el >>> 2) &&& 0x3FFFFFFF
@[inline] def snd (el : Nat) : Nat := el >>> 32

end El

/-- A node index must fit the 30 bits of a stack element. -/
def maxStore : Nat := 0x3FFFFFFF

/-- What the machine needs from the file, laid out for fast access. Binder types are in
the encoding of `Ty`. -/
structure Ctx where
  bytes : ByteArray
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
  return { bytes := f.bytes, sortMods := f.sorts.map (·.raw.toNat), termNargs, termArgs, termRet,
           termRetDeps, termUnify, thmNargs, thmArgs, thmUnify, argTys }

/-- The state of the machine. -/
structure Machine where
  store : Array Nat := #[]
  stack : Array Nat := #[]
  heap : Array Nat := #[]
  /-- The hypotheses declared by `Hyp`, as nodes. -/
  hyps : Array Nat := #[]
  /-- The unify stack. -/
  ustack : Array Nat := #[]
  /-- The unify heap: `2 * node`, plus `1` for an entry made by `UTermSave`. -/
  uheap : Array Nat := #[]
  /-- Scratch: the dependency sets of the bound arguments of the term or theorem being
  applied. -/
  bdeps : Array Nat := #[]
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

/-- Is `d` disjoint from the dependencies of every entry of the unify heap that was not
made by `UTermSave`: the arguments and the earlier dummies? -/
partial def dummyIsFresh (m : Machine) (d : Nat) (i : Nat) : Bool :=
  if i ≥ m.uheap.size then true
  else
    let h := m.uheap[i]!
    if h &&& 1 == 0 && Ty.deps m.store[h >>> 1]! &&& d != 0 then false
    else dummyIsFresh m d (i + 1)

/-- Pushes the arguments of the application node `p` on the unify stack, the first one
on top. -/
partial def pushArgs (p n : Nat) (m : Machine) : Machine :=
  if n == 0 then m
  else pushArgs p (n - 1) { m with ustack := m.ustack.push m.store[p + 1 + n]! }

/-- Runs the unify stream at `pos`. The unify stack holds the target and the unify heap
the substitution. -/
partial def unify (c : Ctx) (mode : UMode) (pos : Nat) : M Unit := fun m =>
  let b := c.bytes
  if pos ≥ b.size then .error "unify: the stream runs past the end of the file" m
  else
    let first := b.get! pos
    let next := pos + cmdSize first
    if next > b.size then .error "unify: the stream runs past the end of the file" m
    else
      let data := cmdData b pos first
      let op := first &&& 0x3F
      if op == 0x32 then
        -- URef i: the top of the unify stack is heap entry i, the same node
        if data ≥ m.uheap.size then .error s!"unify: reference to heap entry {data}, which does not exist" m
        else if m.ustack.size == 0 then .error "unify: stack underflow" m
        else if m.ustack.back! != m.uheap[data]! >>> 1 then
          .error s!"unify failure at 0x{hex pos}: the expression is not the one substituted for heap entry {data}" m
        else unify c mode next { m with ustack := m.ustack.pop }
      else if op == 0x30 || op == 0x31 then
        -- UTerm t: the top is an application of t; replace it by its arguments
        if m.ustack.size == 0 then .error "unify: stack underflow" m
        else
          let p := m.ustack.back!
          if m.store[p + 1]! != data + 1 then
            .error s!"unify failure at 0x{hex pos}: the expression is not an application of term {data}" m
          else
            let m := { m with ustack := m.ustack.pop }
            let m := pushArgs p c.termNargs[data]! m
            let m := if op == 0x31 then { m with uheap := m.uheap.push (2 * p + 1) } else m
            unify c mode next m
      else if op == 0x33 then
        -- UDummy s: the top is a bound variable of sort s, new with respect to the
        -- arguments and the earlier dummies
        if mode != .defn then .error "unify: UDummy outside a definition" m
        else if m.ustack.size == 0 then .error "unify: stack underflow" m
        else
          let p := m.ustack.back!
          let ty := m.store[p]!
          if m.store[p + 1]! != 0 || !Ty.bound ty || Ty.sort ty != data then
            .error s!"unify failure at 0x{hex pos}: a bound variable of sort {data} is expected for a dummy" m
          else if !dummyIsFresh m (Ty.deps ty) 0 then
            .error s!"unify failure at 0x{hex pos}: the variable taken for a dummy also occurs in the arguments or is another dummy" m
          else unify c mode next { m with ustack := m.ustack.pop, uheap := m.uheap.push (2 * p) }
      else if op == 0x36 then
        -- UHyp: the next hypothesis becomes the target
        match mode with
        | .thm =>
          if m.stack.size == 0 then .error "unify: a subproof is missing on the stack" m
          else
            let el := m.stack.back!
            if El.tag el != 1 then .error "unify: expected the proof of a hypothesis on the stack" m
            else unify c mode next { m with stack := m.stack.pop, ustack := m.ustack.push (el >>> 2) }
        | .thmEnd =>
          if m.ustack.size != 0 then .error "unify: the statement is not matched completely before the next hypothesis" m
          else if m.hyps.size == 0 then .error "unify failure: the statement has more hypotheses than the proof declares" m
          else unify c mode next { m with hyps := m.hyps.pop, ustack := m.ustack.push m.hyps.back! }
        | .defn => .error "unify: UHyp in a definition" m
      else if op == 0 then
        if m.ustack.size != 0 then .error "unify: the stream ends before the expression is matched completely" m
        else if mode == .thmEnd && m.hyps.size != 0 then
          .error "unify failure: the proof declares more hypotheses than the statement has" m
        else .ok () m
      else .error s!"unify: unknown command 0x{hex op.toNat}" m

/-- Starts a unification with `target` on the unify stack. -/
@[inline] def unifyWith (c : Ctx) (mode : UMode) (pos target : Nat) : M Unit := do
  modify fun m => { m with ustack := (m.ustack.shrink 0).push target }
  unify c mode pos

/-! ### Proof commands (section 6, "Proof commands") -/

/-- The union of the sets in `bdeps` selected by the bits of `mask`. -/
partial def selectDeps (bdeps : Array Nat) (mask : Nat) (j acc : Nat) : Nat :=
  if j ≥ bdeps.size then acc
  else selectDeps bdeps mask (j + 1) (if (mask >>> j) &&& 1 != 0 then acc ||| bdeps[j]! else acc)

/-- The arguments of `Term t`, taken from the stack at `base`: checks each against its
binder, appends it to the node being built, and returns the dependencies of the term.

In a theorem these are the variables of the term: the union over all arguments
(`HasVar` in `mm0.mm0`). In a definition they are its free variables (`Free`): a bound
argument contributes nothing here, and a regular argument contributes its own minus the
bound arguments its binder is declared to depend on. -/
partial def termArgs (c : Ctx) (isDef : Bool) (off base n i acc : Nat) : M Nat := fun m =>
  if i == n then .ok acc m
  else
    let el := m.stack[base + i]!
    if El.tag el != 0 then .error s!"Term: argument {i} is not an expression" m
    else
      let e := el >>> 2
      let ety := m.store[e]!
      let target := c.argTys[off + i]!
      if Ty.sort ety != Ty.sort target then .error s!"Term: argument {i} has sort {Ty.sort ety}, the binder has sort {Ty.sort target}" m
      else if Ty.bound target && !Ty.bound ety then .error s!"Term: argument {i} must be a bound variable" m
      else
        let d := Ty.deps ety
        let m := { m with store := m.store.push e }
        if !isDef then termArgs c isDef off base n (i + 1) (acc ||| d) m
        else if Ty.bound target then
          termArgs c isDef off base n (i + 1) acc { m with bdeps := m.bdeps.push d }
        else
          let bound := selectDeps m.bdeps (Ty.deps target) 0 0
          termArgs c isDef off base n (i + 1) (acc ||| (d &&& (Ty.depsMask ^^^ bound))) m

/-- `Term t`: `S, e1, ..., en --> S, (t e1 ... en)`; with `save`, also onto the heap. -/
def stepTerm (c : Ctx) (isDef : Bool) (t : Nat) (save : Bool) : M Unit := do
  let m ← get
  if t ≥ m.numTerms then fail s!"Term: term {t} is not declared before this statement"
  let n := c.termNargs[t]!
  if m.stack.size < n then fail "stack underflow"
  let base := m.stack.size - n
  let node := m.store.size
  if node ≥ maxStore then fail "this proof needs more than 2^30 store slots"
  modify fun m => { m with store := (m.store.push 0).push (t + 1), bdeps := m.bdeps.shrink 0 }
  let acc ← termArgs c isDef c.termArgs[t]! base n 0 0
  -- in a definition, the bound arguments that the return type depends on are free
  let m ← get
  let acc := if isDef then selectDeps m.bdeps c.termRetDeps[t]! 0 acc else acc
  modify fun m =>
    { m with store := m.store.set! node (c.termRet[t]! ||| acc),
             stack := (m.stack.shrink base).push (El.expr node) }
  if save then pushHeap (El.expr node)

/-- The substitution of `Thm T`, taken from the stack at `base`: checks each expression
against its binder and the disjoint variable conditions (`safe_subst` in `mm0.lean`), and
loads the unify heap. `seen` is the union of the dependencies of the arguments so far. -/
partial def thmArgs (c : Ctx) (off base n i seen : Nat) : M Unit := fun m =>
  if i == n then .ok () m
  else
    let el := m.stack[base + i]!
    if El.tag el != 0 then .error s!"Thm: argument {i} is not an expression" m
    else
      let e := el >>> 2
      let ety := m.store[e]!
      let target := c.argTys[off + i]!
      if Ty.sort ety != Ty.sort target then .error s!"Thm: argument {i} has sort {Ty.sort ety}, the binder has sort {Ty.sort target}" m
      else if Ty.bound target && !Ty.bound ety then .error s!"Thm: argument {i} must be a bound variable" m
      else
        let d := Ty.deps ety
        if Ty.bound target then
          -- a bound variable must be new with respect to every earlier argument
          if d &&& seen != 0 then
            .error s!"disjoint variable violation: the variable given for the bound argument {i} occurs in an earlier argument" m
          else
            thmArgs c off base n (i + 1) (seen ||| d)
              { m with uheap := m.uheap.push (2 * e), bdeps := m.bdeps.push d }
        else
          -- a regular argument must avoid the bound variables it is not declared to
          -- depend on
          let allowed := selectDeps m.bdeps (Ty.deps target) 0 0
          let all := selectDeps m.bdeps Ty.depsMask 0 0
          if d &&& (all &&& (Ty.depsMask ^^^ allowed)) != 0 then
            .error s!"disjoint variable violation: argument {i} contains a bound variable it is not declared to depend on" m
          else thmArgs c off base n (i + 1) (seen ||| d) { m with uheap := m.uheap.push (2 * e) }

/-- `Thm T`: `S, ⊢ h1, ..., ⊢ hm, e1, ..., en, e --> S, ⊢ e`. -/
def stepThm (c : Ctx) (isDef : Bool) (t : Nat) (save : Bool) : M Unit := do
  if isDef then fail "Thm in a definition"
  if t ≥ (← get).numThms then fail s!"Thm: theorem {t} is not declared before this statement"
  let e ← popExpr
  let n := c.thmNargs[t]!
  let m ← get
  if m.stack.size < n then fail "stack underflow"
  let base := m.stack.size - n
  modify fun m => { m with uheap := m.uheap.shrink 0, bdeps := m.bdeps.shrink 0 }
  thmArgs c c.thmArgs[t]! base n 0 0
  modify fun m => { m with stack := m.stack.shrink base }
  unifyWith c .thm c.thmUnify[t]! e
  push (El.proof e)
  if save then pushHeap (El.proof e)

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

/-- The commands other than `Term`, `Thm` and `Ref`. -/
def stepOther (c : Ctx) (isDef : Bool) (op : UInt8) (data : Nat) : M Unit := do
  if op == 0x13 then
    -- Dummy s: a new bound variable, on the stack and on the heap
    let m ← get
    if data ≥ m.numSorts then fail s!"Dummy: sort {data} is not declared before this statement"
    if c.sortMods[data]! &&& 10 != 0 then fail s!"Dummy: sort {data} is strict or free"
    if m.nextBv ≥ 55 then fail "more than 55 bound variables"
    let e ← allocVar (Ty.mk data true (1 <<< m.nextBv))
    modify fun m => { m with nextBv := m.nextBv + 1 }
    push (El.expr e)
    pushHeap (El.expr e)
  else if op == 0x16 then
    -- Hyp: `HS; H; S, e --> HS, e; H, ⊢ e; S`
    if isDef then fail "Hyp in a definition"
    let e ← popExpr
    let m ← get
    if c.sortMods[Ty.sort m.store[e]!]! &&& 4 == 0 then fail "Hyp: the hypothesis does not have a provable sort"
    modify fun m => { m with hyps := m.hyps.push e }
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

/-- `Ref i`: push heap entry `i`; a saved conversion `e1 = e2` instead discharges the
obligation `e1 =?= e2` on top of the stack. -/
@[inline] def stepRef (i : Nat) : M Unit := fun m =>
  if i ≥ m.heap.size then .error s!"Ref: heap entry {i} does not exist" m
  else
    let el := m.heap[i]!
    if El.tag el != 2 then .ok () { m with stack := m.stack.push el }
    else if m.stack.size == 0 then .error "stack underflow" m
    else if m.stack.back! != el + 1 then
      .error "Ref: the saved conversion is not the obligation on the stack" m
    else .ok () { m with stack := m.stack.pop }

/-- Runs the proof commands in `[pos, stop)`; the last byte of the range is the `END`. -/
partial def runProof (c : Ctx) (isDef : Bool) (pos stop : Nat) : M Unit := fun m =>
  let m := { m with pos := pos }
  if pos ≥ stop then .error "the proof does not end with END" m
  else
    let b := c.bytes
    let first := b.get! pos
    let next := pos + cmdSize first
    let op := first &&& 0x3F
    if op == 0 then
      if pos + 1 == stop then .ok () m else .error "END before the end of the statement's proof" m
    else if next > stop then .error "the proof does not end with END: this command crosses its end" m
    else
      let data := cmdData b pos first
      let result :=
        if op == 0x12 then stepRef data m
        else if op == 0x10 then stepTerm c isDef data false m
        else if op == 0x11 then stepTerm c isDef data true m
        else if op == 0x14 then stepThm c isDef data false m
        else if op == 0x15 then stepThm c isDef data true m
        else stepOther c isDef op data m
      match result with
      | .ok () m => runProof c isDef next stop m
      | .error e m => .error e m

end Whitehead.Verify
