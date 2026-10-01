/-
Checking the statements of a proof file: the binders of every declaration, the proof
body, and what must hold when the body ends (`docs/MMB-NOTES.md` section 6, "End of a
statement"). `checkProofs` walks the whole proof stream.

This checks the proof file on its own, which is what `mm0-rs compile file.mmb` does.
That the file proves a given specification is a separate check (`Whitehead.Verify.Spec`).
-/
import Whitehead.Verify.Machine

namespace Whitehead.Verify

open Whitehead.Mmb

/-- A failed check: where in the file, in which statement, and why. -/
structure VerifyError where
  pos : Nat
  msg : String
  /-- The index of the statement in `MmbFile.stmts`, if the error is inside one. -/
  stmt : Option Nat
  deriving Inhabited

/-- `sort wff`, `def dbl`, `theorem T12`: what a statement declares. -/
def stmtLabel (f : MmbFile) (s : Stmt) : String :=
  match s.kind with
  | .sort => s!"sort {f.sortName s.index}"
  | .termDef _ => (if f.terms[s.index]!.isDef then "def " else "term ") ++ f.termName s.index
  | .ax => s!"axiom {f.thmName s.index}"
  | .thm _ => s!"theorem {f.thmName s.index}"

/-- `file:0x<offset>: error: in theorem foo: msg` -/
def VerifyError.format (e : VerifyError) (f : MmbFile) (file : String) : String :=
  let where_ := match e.stmt.bind (f.stmts[·]?) with
    | some s => s!"in {stmtLabel f s}: "
    | none => ""
  s!"{file}:0x{hex e.pos}: error: {where_}{e.msg}"

/-- The binders of a declaration: checks them and puts one variable per binder on the
heap. A bound variable must not have a strict sort and owns the next dependency bit; a
regular variable may depend only on bound variables declared before it (`ctx.ok` in
`mm0.lean`). -/
def loadArgs (c : Ctx) (args : Array Arg) : M Unit := do
  for i in [0:args.size] do
    let a := args[i]!
    let m ← get
    if a.sort ≥ m.numSorts then
      fail s!"binder {i}: sort {a.sort} is not declared before this statement"
    if a.bound then
      if c.sortMods[a.sort]! &&& 2 != 0 then
        fail s!"binder {i}: a bound variable cannot have a strict sort"
      if m.nextBv ≥ 55 then
        fail "more than 55 bound variables"
      if a.deps != (1 : UInt64) <<< m.nextBv.toUInt64 then
        fail s!"binder {i}: the dependencies of a bound variable must be exactly its own bit"
      modify fun m => { m with nextBv := m.nextBv + 1 }
    else if a.deps >>> m.nextBv.toUInt64 != 0 then
      fail s!"binder {i}: it depends on a bound variable that is not declared before it"
    let e ← allocVar (Ty.ofArg a)
    pushHeap (El.expr e)

/-- The first `n` heap entries, which are the variables of the declaration, as the unify
heap. -/
def argsAsUheap (n : Nat) (m : Machine) : Machine := Id.run do
  let mut uheap := m.uheap.shrink 0
  for i in [0:n] do
    uheap := uheap.push (2 * (m.heap[i]! >>> 2))
  return { m with uheap }

/-- A `Term`, `Def` or `LocalDef` statement. -/
def checkTerm (c : Ctx) (f : MmbFile) (s : Stmt) (isLocal : Bool) : M Unit := do
  let t := s.index
  let entry := f.terms[t]!
  if isLocal && !entry.isDef then
    fail "a local statement must be a def or a theorem; a term must be declared in the specification"
  loadArgs c (f.termArgs t)
  let ret := f.termRet t
  let m ← get
  if ret.bound then
    fail "the return type is marked as a bound variable"
  if ret.sort ≥ m.numSorts then
    fail s!"the result sort {ret.sort} is not declared before this statement"
  if ret.sort != entry.sort then
    fail s!"the term table gives the result sort {entry.sort}, the return type gives sort {ret.sort}"
  if c.sortMods[ret.sort]! &&& 1 != 0 then
    fail "a term cannot have a pure sort as its result"
  if ret.deps >>> m.nextBv.toUInt64 != 0 then
    fail "the return type depends on a bound variable that the term does not have"
  if entry.isDef then
    -- the body builds the value; it must be an expression of the result sort whose free
    -- variables are declared by the return type (`defn_ok`), and it must be the
    -- expression that the unify stream of the definition describes
    runProof c true s.bodyStart s.stop
    let m ← get
    if m.stack.size != 1 then
      fail s!"the body of a definition must leave exactly one expression on the stack; it leaves {m.stack.size} elements"
    let el := m.stack[0]!
    if El.tag el != 0 then
      fail "the body of a definition must leave an expression on the stack"
    let e := el >>> 2
    let ty := m.store[e]!
    if Ty.sort ty != ret.sort then
      fail s!"the value has sort {Ty.sort ty}, the definition has result sort {ret.sort}"
    if Ty.minus (Ty.deps ty) ret.deps.toNat != 0 then
      fail "the value has free variables that the return type does not declare"
    modify (argsAsUheap entry.numArgs)
    unifyWith c .defn (f.termUnifyPos t) e
  modify fun m => { m with numTerms := m.numTerms + 1 }

/-- An `Axiom`, `Thm` or `LocalThm` statement. -/
def checkThm (c : Ctx) (f : MmbFile) (s : Stmt) (isAxiom : Bool) : M Unit := do
  let t := s.index
  loadArgs c (f.thmArgs t)
  runProof c false s.bodyStart s.stop
  let m ← get
  if m.stack.size != 1 then
    fail s!"the body must leave exactly one element on the stack; it leaves {m.stack.size}"
  let el := m.stack[0]!
  if isAxiom then
    if El.tag el != 0 then fail "the body of an axiom must leave its statement, an expression, on the stack"
  else if El.tag el != 1 then
    fail "the body of a theorem must leave a proof on the stack"
  let e := el >>> 2
  if c.sortMods[Ty.sort m.store[e]!]! &&& 4 == 0 then
    fail "the conclusion does not have a provable sort"
  -- what was built must be the statement that the unify stream describes
  modify (argsAsUheap f.thms[t]!.numArgs)
  unifyWith c .thmEnd (f.thmUnifyPos t) e
  modify fun m => { m with numThms := m.numThms + 1 }

/-- One statement, on a machine whose store, stack, heap and hypotheses are empty. -/
def checkStmt (c : Ctx) (f : MmbFile) (s : Stmt) : M Unit :=
  match s.kind with
  | .sort => modify fun m => { m with numSorts := m.numSorts + 1 }
  | .termDef isLocal => checkTerm c f s isLocal
  | .ax => checkThm c f s true
  | .thm _ => checkThm c f s false

/-- The machine made ready for the statement at `pos`. The arrays keep their memory. -/
def Machine.reset (m : Machine) (pos : Nat) : Machine :=
  { m with store := m.store.shrink 0, stack := m.stack.shrink 0, heap := m.heap.shrink 0,
           hyps := m.hyps.shrink 0, nextBv := 0, pos }

/-- Checks every statement of the proof stream. -/
def checkProofs (f : MmbFile) : Except VerifyError Unit := do
  let c := Ctx.ofFile f
  let mut m : Machine := {}
  for i in [0:f.stmts.size] do
    let s := f.stmts[i]!
    match checkStmt c f s (m.reset s.pos) with
    | .ok () m' => m := m'
    | .error msg m' => throw { pos := m'.pos, msg, stmt := some i }
  -- every entry of the tables must have been declared
  let h := f.header
  if m.numSorts != h.numSorts || m.numTerms != h.numTerms || m.numThms != h.numThms then
    throw { pos := h.pProof, stmt := none,
            msg := s!"the proof stream declares {m.numSorts} sorts, {m.numTerms} terms and {m.numThms} theorems; the header has {h.numSorts}, {h.numTerms} and {h.numThms}" }

end Whitehead.Verify
