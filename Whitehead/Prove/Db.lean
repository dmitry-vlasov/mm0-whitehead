/-
The prover's view of a proof file: the terms, and every axiom and theorem as an
assertion over expressions (`Whitehead/Prove/Exp.lean`), with the conditions on its
bound variables. This is what Russell has in `RuMath` and `RuAssertion`
(`src/ru/src.flow`); the statement to be proved with its variables turned into
constants is the port of `ruConstProverTask` (`src/ru/prover/core/util.flow`).

Numbering of variables. The binders of an assertion are the variables `0, 1, ...` of
that assertion; all assertions share these numbers, which is harmless because the
variables of an assertion never get into the tree (`ruExpandHyp` replaces every one of
them). The variables that the prover makes have numbers from `freshBase` on.
-/
import Whitehead.Mmb.Reader
import Whitehead.Prove.Index

namespace Whitehead.Prove

open Whitehead.Mmb

/-- The first number of the variables made by the prover. A statement has fewer than
2^16 binders. -/
def freshBase : Nat := 0x10000

/-- The value of a `def f (xs) {.ys}: s = B`: `B` over the arguments, which are the
variables `0 .. n-1` as in an assertion, and the dummies, which are the variables
`n, n+1, ...`, names of their sorts. -/
structure DefValue where
  dummies : Array Nat
  expr : Exp
  deriving Inhabited

structure TermInfo where
  name : String
  /-- The type of an application of the term. -/
  ty : Nat
  /-- The types of the arguments: names for the bound ones. -/
  args : Array Nat
  /-- For a def, its value. -/
  value : Option DefValue := none
  deriving Inhabited

/-- An axiom or a theorem. -/
structure Assertion where
  /-- Its number in the theorem table of the file. -/
  id : Nat
  name : String
  binders : Array Arg
  /-- The variable of each binder. -/
  vars : Array Nat
  hyps : Array Exp
  concl : Exp
  /-- The pairs `(x, v)` of binders, `x` a bound one: what is given for `x` must not
  occur in what is given for `v` (`docs/DESIGN.md`, "Where MM0 differs"). A pair of two
  bound binders is listed once. -/
  disjs : Array (Nat × Nat)
  /-- How many sorts and terms are declared before it. -/
  sortsBefore : Nat := 0
  termsBefore : Nat := 0
  deriving Inhabited

structure Db where
  file : MmbFile
  terms : Array TermInfo
  /-- The terms that are defs, in order. -/
  defs : Array Nat
  /-- By the number in the theorem table, which is the order of declaration. -/
  asserts : Array Assertion
  deriving Inhabited

/-- The type of a binder or of a return type. -/
def argTy (a : Arg) : Nat := Ty.mk a.sort a.bound

/-- A pattern of a unify stream as an expression. `heap` holds the expression of every
heap entry of the stream so far. -/
partial def patternExp (terms : Array TermInfo) (p : Pattern) (heap : Array Exp) :
    Except String (Exp × Array Exp) := do
  match p with
  | .ref i =>
    match heap[i]? with
    | some e => return (e, heap)
    | none => throw s!"reference to heap entry {i}, which does not exist"
  | .dummy _ _ => throw "a dummy in the statement of an axiom or theorem"
  | .app t save args =>
    let some info := terms[t]? | throw s!"term {t} does not exist"
    if info.args.size != args.size then throw s!"term {info.name}: wrong number of arguments"
    -- the entry of a saved term comes before those of its arguments
    let slot := heap.size
    let mut heap := if save.isSome then heap.push default else heap
    let mut es := Array.mkEmpty args.size
    for a in args do
      let (e, h) ← patternExp terms a heap
      es := es.push e
      heap := h
    let e := Exp.mkApp t info.ty es
    if e.size > Node.maxLen then throw "an expression of more than 2^30 nodes"
    if save.isSome then heap := heap.set! slot e
    return (e, heap)

/-- The value of a def as an expression (`patternExp` for a def's stream): `nd` dummies
have been seen; a dummy becomes the next variable after the `numArgs` arguments. -/
partial def valueExp (terms : Array TermInfo) (numArgs : Nat) (p : Pattern) (heap : Array Exp) (nd : Nat) :
    Except String (Exp × Array Exp × Nat) := do
  match p with
  | .ref i =>
    match heap[i]? with
    | some e => return (e, heap, nd)
    | none => throw s!"reference to heap entry {i}, which does not exist"
  | .dummy sort _ =>
    let e := Exp.ofVar (Node.var (numArgs + nd) (Ty.mk sort true))
    return (e, heap.push e, nd + 1)
  | .app t save args =>
    let some info := terms[t]? | throw s!"term {t} does not exist"
    if info.args.size != args.size then throw s!"term {info.name}: wrong number of arguments"
    let slot := heap.size
    let mut heap := if save.isSome then heap.push default else heap
    let mut nd := nd
    let mut es := Array.mkEmpty args.size
    for a in args do
      let (e, h, n) ← valueExp terms numArgs a heap nd
      es := es.push e
      heap := h
      nd := n
    let e := Exp.mkApp t info.ty es
    if e.size > Node.maxLen then throw "an expression of more than 2^30 nodes"
    if save.isSome then heap := heap.set! slot e
    return (e, heap, nd)

/-- The pairs of binders that must be kept apart. -/
def disjPairs (binders : Array Arg) : Array (Nat × Nat) := Id.run do
  -- the number of each bound binder among the bound ones: its bit in `deps`
  let mut bit : Array Nat := #[]
  let mut k := 0
  for b in binders do
    bit := bit.push k
    if b.bound then k := k + 1
  let mut out := #[]
  for i in [0:binders.size] do
    if binders[i]!.bound then
      for j in [0:binders.size] do
        if j != i then
          let v := binders[j]!
          if v.bound then
            if i < j then out := out.push (i, j)
          else if (v.deps >>> bit[i]!.toUInt64) &&& 1 == 0 then
            out := out.push (i, j)
  return out

/-- The assertions and terms of a proof file. -/
def Db.ofFile (f : MmbFile) : Except String Db := do
  if f.terms.size ≥ Node.constBase then throw "more than 2^23 terms"
  let mut terms := (Array.range f.terms.size).map fun t =>
    ({ name := f.termName t, ty := Ty.mk (f.termRet t).sort false, args := (f.termArgs t).map argTy } : TermInfo)
  -- the values of the defs, which refer to the terms before them
  let mut defs := #[]
  for t in [0:f.terms.size] do
    if f.terms[t]!.isDef then
      match f.termValue t with
      | .error e => throw s!"def {f.termName t}: 0x{hex e.pos}: {e.msg}"
      | .ok st =>
        let numArgs := terms[t]!.args.size
        let heap := (Array.range numArgs).map fun k => Exp.ofVar (Node.var k terms[t]!.args[k]!)
        let (expr, _, nd) ← (valueExp terms numArgs st.concl heap 0).mapError (s!"def {f.termName t}: " ++ ·)
        let dummies := (Array.range nd).map fun j => Node.var (numArgs + j) (Ty.mk st.dummies[j]! true)
        terms := terms.modify t fun info => { info with value := some { dummies, expr } }
        defs := defs.push t
  -- what is declared before each theorem
  let mut before : Array (Nat × Nat) := Array.replicate f.thms.size (0, 0)
  let mut nSorts := 0
  let mut nTerms := 0
  for s in f.stmts do
    match s.kind with
    | .sort => nSorts := nSorts + 1
    | .termDef _ => nTerms := nTerms + 1
    | _ => before := before.set! s.index (nSorts, nTerms)
  let mut asserts := Array.mkEmpty f.thms.size
  for i in [0:f.thms.size] do
    let binders := f.thmArgs i
    let vars := (Array.range binders.size).map fun k => Node.var k (argTy binders[k]!)
    match f.thmStatement i with
    | .error e => throw s!"theorem {f.thmName i}: 0x{hex e.pos}: {e.msg}"
    | .ok st =>
      -- heap entries are numbered in the order of the stream: the conclusion, then the
      -- hypotheses from the last to the first
      let mut heap := vars.map Exp.ofVar
      let (concl, h) ← (patternExp terms st.concl heap).mapError (s!"theorem {f.thmName i}: " ++ ·)
      heap := h
      let mut hyps : Array Exp := Array.replicate st.hyps.size default
      for k in [0:st.hyps.size] do
        let j := st.hyps.size - 1 - k
        let (e, h) ← (patternExp terms st.hyps[j]! heap).mapError (s!"theorem {f.thmName i}: " ++ ·)
        hyps := hyps.set! j e
        heap := h
      asserts := asserts.push
        { id := i, name := f.thmName i, binders, vars, hyps, concl, disjs := disjPairs binders,
          sortsBefore := before[i]!.1, termsBefore := before[i]!.2 }
  return { file := f, terms, defs, asserts }

namespace Db

/-- The name of a term, or of the constant that stands for binder `k` of a statement
being proved (`names` are those of its binders). -/
def termName (db : Db) (names : Array String := #[]) (id : Nat) : String :=
  if id ≥ Node.constBase then names[id - Node.constBase]?.getD s!"c{id - Node.constBase}"
  else (db.terms[id]?.map (·.name)).getD s!"t{id}"

def varName (id : Nat) : String :=
  if id ≥ freshBase then s!"?{id - freshBase}" else s!"v{id}"

def showExp (db : Db) (e : Exp) (names : Array String := #[]) : String :=
  e.toSexp (db.termName names) varName

/-- The value of def `t` with `args` for its arguments and `dummies` for its dummies. -/
def unfolded (db : Db) (t : Nat) (args dummies : Array Exp) : Exp :=
  match db.terms[t]!.value with
  | none => default
  | some v =>
    let n := args.size
    let info := db.terms[t]!
    let map : Std.HashMap Nat SubExp := (Array.range (n + dummies.size)).foldl (init := {}) fun m k =>
      if k < n then m.insert k (SubExp.mk' (Node.var k info.args[k]!) args[k]!)
      else m.insert k (SubExp.mk' v.dummies[k - n]! dummies[k - n]!)
    ({ map } : Subst).apply v.expr

/-- The index of the conclusions of all assertions, each ranked by its number. -/
def index (db : Db) : Index Nat :=
  db.asserts.foldl (init := {}) fun ix a => ix.insert a.concl a.id a.id

end Db

/-- The hypotheses of all assertions, for the forward direction: those of the
assertions with one hypothesis (`RuProverForward.hypIndex`), and of the others every
hypothesis that is not a bare variable, with its position (`multiHyp`). A bare variable
unifies with every fact, so it is not a trigger; it is filled from the front. Each is
ranked by the number of its assertion. -/
structure HypIndexes where
  single : Index Nat := {}
  multi : Index (Nat × Nat) := {}
  deriving Inhabited

/-- `ruInitProverForwardProved`, the part that does not depend on the task. -/
def Db.hypIndexes (db : Db) : HypIndexes :=
  db.asserts.foldl (init := {}) fun ix a =>
    if a.hyps.size == 1 then { ix with single := ix.single.insert a.hyps[0]! a.id a.id }
    else
      (Array.range a.hyps.size).foldl (init := ix) fun ix i =>
        if a.hyps[i]!.isVar then ix else { ix with multi := ix.multi.insert a.hyps[i]! (a.id, i) a.id }

/-! ### The statement to be proved -/

/-- A variable of the statement to be proved, as the constant that stands for it. -/
structure ConstInfo where
  ty : Nat
  /-- The bound variables it stands for or depends on: itself, for a bound variable;
  the declared dependencies, for a regular one. As numbers of constants. -/
  names : Array Nat
  deriving Inhabited

/-- `RuProverTask`: premises and a goal. A variable of the statement to be proved is
either a *free variable* — the proof must hold for every value of it, so the prover must
not replace it, and it is a constant here — or a *metavariable*: the prover has to find
a value for it, and it is a variable of the tree. -/
structure Task where
  /-- The assertions that may be used are those with a smaller number. -/
  limit : Nat
  /-- The sorts and terms that may be used are those with smaller numbers. -/
  sorts : Nat
  terms : Nat
  consts : Array ConstInfo
  premises : Array Exp
  goal : Exp
  /-- The metavariables: variables with the numbers `freshBase`, `freshBase + 1`, ...,
  which the prover leaves to them (`Env.init`). -/
  metas : Array Nat := #[]
  deriving Inhabited

/-- The constants for the binders of a statement. -/
def constInfos (binders : Array Arg) : Array ConstInfo := Id.run do
  -- the positions of the bound binders, in the order of their bits
  let boundAt := (Array.range binders.size).filter fun i => binders[i]!.bound
  (Array.range binders.size).map fun i =>
    let b := binders[i]!
    if b.bound then { ty := argTy b, names := #[i] }
    else
      { ty := argTy b,
        names := (Array.range boundAt.size).filterMap fun k =>
          if (b.deps >>> k.toUInt64) &&& 1 != 0 then some boundAt[k]! else none }

/-- Why the binders with the numbers `metas` of theorem `thm` cannot all be marked as
metavariables, if they cannot. Only a regular binder can be marked. For a bound one,
the regular variables that are declared to depend on it would depend on whatever is
found for it, and the conditions on bound variables (`judge` in `Proofs.lean`) read the
dependencies of a constant as fixed. -/
def Db.metasFault (db : Db) (thm : Nat) (metas : Array Nat) : Option String :=
  let a := db.asserts[thm]!
  metas.findSome? fun k =>
    match a.binders[k]? with
    | none => some s!"theorem {a.name} has no binder {k}: it has {a.binders.size}"
    | some b => if b.bound then some s!"binder {k} of theorem {a.name} is a bound variable" else none

/-- `ruConstProverTask`, for a theorem of the file: prove its conclusion from its
hypotheses, with what comes before it. The variables of the theorem are free variables,
and become constants. The binders with the numbers `metas` are marked as metavariables
instead; the marks that `Db.metasFault` objects to are not followed.

Where the marks come from is a stub. MM0 has no syntax to say of a variable of a
statement that it is a metavariable, so a file cannot carry them, and a caller gives
them by the number of the binder (`prove search --meta`). A proof found for a task with
metavariables proves an instance of the theorem, which is not a statement of the file:
it is reported, and not written or checked (`acceptAny` in `Prove.lean`). -/
def Db.task (db : Db) (thm : Nat) (metas : Array Nat := #[]) : Task :=
  let a := db.asserts[thm]!
  let marked := (Array.range a.binders.size).filter fun k => metas.contains k && !a.binders[k]!.bound
  let image (v : Nat) : Exp :=
    match marked.findIdx? (· == Node.varId v) with
    | some j => Exp.ofVar (Node.var (freshBase + j) (Node.ty v))
    | none => ⟨#[Node.const (Node.varId v) (Node.ty v)]⟩
  let s : Subst := { map := a.vars.foldl (init := {}) fun m v => m.insert (Node.varId v) (SubExp.mk' v (image v)) }
  { limit := thm, sorts := a.sortsBefore, terms := a.termsBefore, consts := constInfos a.binders,
    premises := a.hyps.map s.apply, goal := s.apply a.concl,
    metas := marked.map fun k => (image a.vars[k]!).nodes[0]! }

/-! ### Proofs of the file as trees of assertions -/

/-- What a proof body says about which assertions are used, and nothing else: the tree
of the applications, with the hypotheses of the theorem as leaves. This is the "sequence
of statements used" of the replay test. Subproofs that the body refers to twice are one
object here, but a tree to whoever walks it. -/
inductive Skeleton where
  | hyp (i : Nat)
  | step (thm : Nat) (children : Array Skeleton)
  /-- The statement is `child`'s with def `term` unfolded (or folded) at `path`. -/
  | conv (term : Nat) (path : Array Nat) (unfold : Bool) (child : Skeleton)
  deriving Inhabited

namespace Skeleton

/-- The number of steps, counting a shared subproof every time it is used; capped at
`cap`. -/
partial def size (s : Skeleton) (cap : Nat := 1000000000) : Nat :=
  match s with
  | .hyp _ => 0
  | .step _ children => Id.run do
    let mut n := 1
    for c in children do
      if n < cap then n := n + c.size (cap - n)
    return n
  | .conv _ _ _ child => 1 + child.size cap

end Skeleton

/-- An unfolding as the skeleton reader collects it: the def, the path, and whether it is
an unfolding of the statement being proved (else a folding). -/
abbrev ConvStep := Nat × Array Nat × Bool

/-- What the stack holds while a proof body is read with its expressions. -/
inductive SkItem where
  | expr (e : Exp)
  | proof (e : Exp) (sk : Skeleton)
  /-- `⊢ e1` made by `Conv`, whose conversion is still being read: slot `k`. -/
  | pending (e1 : Exp) (k : Nat)
  /-- The obligation `left =?= right` of the conversion in slot `k`, at `path` from the
  statement; `flipped` if `left` is on the side of the proved statement, not the goal. -/
  | obl (left right : Exp) (k : Nat) (path : Array Nat) (flipped : Bool)
  deriving Inhabited

/-- A `Conv` being read: the unfoldings found on the side of the goal and on the side
of the proved statement, how many obligations are open, and the proof converted. -/
structure SkSlot where
  unfolds : Array ConvStep := #[]
  folds : Array ConvStep := #[]
  open_ : Nat := 1
  sk : Skeleton
  deriving Inhabited

/-- The skeleton of a proof body with conversions. The expressions are tracked, so that a
conversion can be read as single unfoldings with their places: at `Unfold`, the def and
the path of the obligation are one step — an unfolding of the goal if the obligation
has the goal's side on the left, a folding otherwise. The steps of a `Conv` are chained
in the order they are applied to the goal: the unfoldings as found (an inner one after
the outer), then the foldings in reverse (an inner one before the outer). `ConvCut` and
`ConvSave`, which share a conversion, are not read: `none`. -/
def skeletonWithConvs (db : Db) (a : Assertion) (cmds : Array ProofCmd) : Except String (Option Skeleton) := do
  let mut stack : Array SkItem := #[]
  let mut heap : Array SkItem := a.vars.map fun v => .expr (Exp.ofVar v)
  let mut slots : Array SkSlot := #[]
  let mut hyps := 0
  let mut dummies := 0
  let popExpr (stack : Array SkItem) : Except String (Exp × Array SkItem) :=
    match stack.back? with
    | some (.expr e) => .ok (e, stack.pop)
    | _ => .error "expected an expression on the stack"
  let popObl (stack : Array SkItem) : Except String (SkItem × Array SkItem) :=
    match stack.back? with
    | some (it@(.obl ..)) => .ok (it, stack.pop)
    | _ => .error "expected an obligation on the stack"
  -- the last obligation of a slot closed: the pending proof below becomes a proof
  let finish (slots : Array SkSlot) (stack : Array SkItem) (k : Nat) : Except String (Array SkItem) :=
    match stack.back? with
    | some (.pending e1 k') =>
      if k' != k then .error "the conversions are not nested"
      else
        let slot := slots[k]!
        let steps := slot.unfolds ++ slot.folds.reverse
        let sk := steps.foldr (init := slot.sk) fun (t, path, unfold) sk => .conv t path unfold sk
        .ok (stack.pop.push (.proof e1 sk))
    | _ => .error "the obligations of a conversion are not above its proof"
  for c in cmds do
    match c with
    | .term t save =>
      let n := db.terms[t]!.args.size
      if stack.size < n then throw "stack underflow"
      let mut args : Array Exp := #[]
      for k in [0:n] do
        match stack[stack.size - n + k]! with
        | .expr e => args := args.push e
        | _ => throw "Term: an argument is not an expression"
      let e := Exp.mkApp t db.terms[t]!.ty args
      stack := (stack.shrink (stack.size - n)).push (.expr e)
      if save then heap := heap.push (.expr e)
    | .ref i =>
      let some item := heap[i]? | throw s!"Ref {i}: no such heap entry"
      stack := stack.push item
    | .dummy sort =>
      let e := Exp.ofVar (Node.var (freshBase + dummies) (Ty.mk sort true))
      dummies := dummies + 1
      stack := stack.push (.expr e)
      heap := heap.push (.expr e)
    | .hyp =>
      let (e, st) ← popExpr stack
      stack := st
      heap := heap.push (.proof e (.hyp hyps))
      hyps := hyps + 1
    | .thm t save =>
      let b := db.asserts[t]!
      let need := b.hyps.size + b.binders.size + 1
      if stack.size < need then throw "stack underflow"
      let base := stack.size - need
      let mut children := #[]
      for k in [0:b.hyps.size] do
        match stack[base + k]! with
        | .proof _ sk => children := children.push sk
        | _ => throw s!"Thm {b.name}: a subproof is missing"
      let (concl, _) ← popExpr stack
      let proof := SkItem.proof concl (.step t children)
      stack := (stack.shrink base).push proof
      if save then heap := heap.push proof
    | .conv =>
      let some (.proof e2 sk) := stack.back? | throw "Conv: expected a proof on the stack"
      let (e1, st) ← popExpr stack.pop
      let k := slots.size
      slots := slots.push { sk }
      stack := (st.push (.pending e1 k)).push (.obl e1 e2 k #[] false)
    | .refl =>
      let (.obl _ _ k _ _, st) ← popObl stack | throw "Refl"
      stack := st
      slots := slots.modify k fun sl => { sl with open_ := sl.open_ - 1 }
      if slots[k]!.open_ == 0 then stack ← finish slots stack k
    | .symm =>
      let (.obl l r k path fl, st) ← popObl stack | throw "Symm"
      stack := st.push (.obl r l k path !fl)
    | .cong =>
      let (.obl l r k path fl, st) ← popObl stack | throw "Cong"
      stack := st
      let ls := l.argStarts 0
      let rs := r.argStarts 0
      if ls.size != rs.size then throw "Cong: the two sides differ in arity"
      -- the first argument ends on top
      for j in [0:ls.size] do
        let i := ls.size - 1 - j
        stack := stack.push (.obl (l.sub ls[i]!) (r.sub rs[i]!) k (path.push i) fl)
      slots := slots.modify k fun sl => { sl with open_ := sl.open_ + ls.size - 1 }
      if slots[k]!.open_ == 0 then stack ← finish slots stack k
    | .unfold =>
      let (e, st) ← popExpr stack
      let (.obl l r k path fl, st) ← popObl st | throw "Unfold"
      let t := Node.appId l.nodes[0]!
      slots := slots.modify k fun sl =>
        if fl then { sl with folds := sl.folds.push (t, path, false) }
        else { sl with unfolds := sl.unfolds.push (t, path, true) }
      stack := st.push (.obl e r k path fl)
    | .convCut | .convSave => return none
    | .save =>
      match stack.back? with
      | some (it@(.expr _)) | some (it@(.proof ..)) => heap := heap.push it
      | _ => throw "Save: the top of the stack cannot be saved"
    | .sorry => throw "Sorry"
  match stack.back? with
  | some (.proof _ proof) => return some proof
  | _ => throw "the body does not leave a proof"

/-- The skeleton of the proof of theorem statement `s`. The body is run on a stack that
only tells expressions from proofs; a body with conversions is read again with its
expressions (`skeletonWithConvs`), which is what a conversion needs. `none` for a body
that shares a conversion (`ConvCut`), which is not supported. -/
def Db.skeleton (db : Db) (s : Stmt) : Except String (Option Skeleton) := do
  let f := db.file
  let cmds ← (f.proofCmds s).mapError fun e => s!"0x{hex e.pos}: {e.msg}"
  let a := db.asserts[s.index]!
  if cmds.any fun c => match c with | .conv | .refl | .symm | .cong | .unfold | .convCut | .convSave => true | _ => false then
    return ← skeletonWithConvs db a cmds
  -- an expression is `none`, a proof is its skeleton
  let mut stack : Array (Option Skeleton) := #[]
  let mut heap : Array (Option Skeleton) := Array.replicate a.binders.size none
  let mut hyps := 0
  for c in cmds do
    match c with
    | .term t save =>
      let n := db.terms[t]!.args.size
      if stack.size < n then throw "stack underflow"
      stack := (stack.shrink (stack.size - n)).push none
      if save then heap := heap.push none
    | .ref i =>
      let some item := heap[i]? | throw s!"Ref {i}: no such heap entry"
      stack := stack.push item
    | .dummy _ =>
      stack := stack.push none
      heap := heap.push none
    | .hyp =>
      if stack.isEmpty then throw "stack underflow"
      stack := stack.pop
      heap := heap.push (some (.hyp hyps))
      hyps := hyps + 1
    | .thm t save =>
      let b := db.asserts[t]!
      let need := b.hyps.size + b.binders.size + 1
      if stack.size < need then throw "stack underflow"
      let base := stack.size - need
      let children := (Array.range b.hyps.size).filterMap fun k => stack[base + k]!
      if children.size != b.hyps.size then throw s!"Thm {b.name}: a subproof is missing"
      let proof := Skeleton.step t children
      stack := (stack.shrink base).push (some proof)
      if save then heap := heap.push (some proof)
    | _ => return none
  match stack.back? with
  | some (some proof) => return some proof
  | _ => throw "the body does not leave a proof"

end Whitehead.Prove
