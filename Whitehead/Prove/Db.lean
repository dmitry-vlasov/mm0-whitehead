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

/-- A rule of the conversion judgment `a ≡ b` of MM0, made into an assertion (`convRules`).
The judgment is written with the terms `≡` and `≡'` (`ConvRules.eq`); `≡'` is the same
judgment with at least one unfolding or folding in its proof. -/
inductive Pseudo where
  /-- `b, a ≡' b ⊢ a`: the proof command `Conv`. -/
  | conv
  /-- `a ≡ a`: `Refl`. -/
  | refl
  /-- `a1 ≡ b1, ... ⊢ t(as) ≡ t(bs)`: `Cong`. -/
  | cong (t : Nat)
  /-- `B ≡ b ⊢ f(xs) ≡ b`, `B` the value of `f`: `Unfold`. -/
  | unfold (f : Nat)
  /-- `a ≡ B ⊢ a ≡ f(xs)`: `Symm`, `Unfold`, `Symm`. -/
  | fold (f : Nat)
  deriving BEq, Inhabited

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
  /-- Its rank in the index of conclusions: theorem `k` may use what has a rank below
  `2k + 1` (`rankLimit`). An assertion of the file has `2 id + 1`; a conversion rule
  `2 r`, `r` being the number of assertions declared before the last term it mentions. -/
  rank : Nat := 0
  /-- For a conversion rule, which one; `none` for an assertion of the file. -/
  pseudo : Option Pseudo := none
  deriving Inhabited

/-- The rank limit of theorem `k` in the index of conclusions (`Assertion.rank`). -/
def rankLimit (k : Nat) : Nat := 2 * k + 1

/-- The conversion rules of a file with defs, by what they are for. -/
structure ConvRules where
  /-- The first term number of the judgment: `≡` of sort `s` is `base + 2 s`, `≡'` is
  `base + 2 s + 1`. -/
  base : Nat := 0
  conv : Std.HashMap Nat Nat := {}
  refl : Std.HashMap Nat Nat := {}
  cong : Std.HashMap Nat Nat := {}
  /-- By the term and the argument position that carries the unfolding. -/
  congS : Std.HashMap (Nat × Nat) Nat := {}
  unfold : Std.HashMap Nat Nat := {}
  unfoldS : Std.HashMap Nat Nat := {}
  fold : Std.HashMap Nat Nat := {}
  foldS : Std.HashMap Nat Nat := {}
  deriving Inhabited

/-- The type of a judgment `a ≡ b`: a sort that no file has. -/
def judgmentTy : Nat := Ty.mk 127 false

/-- `a ≡ b` (`strict`: `a ≡' b`) in sort `s`. -/
def ConvRules.eq (r : ConvRules) (s : Nat) (strict : Bool) (a b : Exp) : Exp :=
  Exp.mkApp (r.base + 2 * s + (if strict then 1 else 0)) judgmentTy #[a, b]

structure Db where
  file : MmbFile
  terms : Array TermInfo
  /-- The terms that are defs, in order. -/
  defs : Array Nat
  /-- The conversion rules, if the file has defs: their assertions are in `asserts`
  after those of the file. -/
  conv : ConvRules := {}
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

/-- The conversion judgment of MM0 as assertions, for a file with defs
(`docs/DESIGN.md`, "Unfolding inside a variable"). The terms `≡` and `≡'` of every sort
are added after the terms of the file, and these rules after its assertions:

    conv_s   b, a ≡' b ⊢ a                     every provable sort s
    refl_s   ⊢ a ≡ a                           every sort s
    cong_t   a1 ≡ b1, ... ⊢ t(as) ≡ t(bs)      every term t with a regular argument; a
                                               bound argument is the same on both sides
    cong'_ti the same with ≡' at position i and in the conclusion
    unfold_f B ≡ b ⊢ f(xs) ≡ b                 every def f, B its value
    fold_f   a ≡ B ⊢ a ≡ f(xs)
    unfold'_f, fold'_f  the same with ≡' in the conclusion

The dummies of `f` are bound variables of `unfold_f` and `fold_f`, kept apart from the
arguments and from each other, which is what the verifier checks at `Unfold`. -/
def convRules (f : MmbFile) (terms : Array TermInfo) (termAfter : Array Nat) (asserts : Array Assertion) :
    Array TermInfo × Array Assertion × ConvRules := Id.run do
  let numSorts := f.sorts.size
  let base := terms.size
  let mut terms := terms
  for s in [0:numSorts] do
    let ty := Ty.mk s false
    terms := terms.push { name := s!"≡{f.sortName s}", ty := judgmentTy, args := #[ty, ty] }
    terms := terms.push { name := s!"≡'{f.sortName s}", ty := judgmentTy, args := #[ty, ty] }
  let mut r : ConvRules := { base }
  let mut asserts := asserts
  let v (k ty : Nat) : Exp := Exp.ofVar (Node.var k ty)
  let add (asserts : Array Assertion) (name : String) (vars : Array Nat) (hyps : Array Exp) (concl : Exp)
      (disjs : Array (Nat × Nat)) (pseudo : Pseudo) (rank : Nat) : Array Assertion × Nat :=
    (asserts.push { id := asserts.size, name, binders := #[], vars, hyps, concl, disjs, rank := 2 * rank,
                    pseudo := some pseudo }, asserts.size)
  for s in [0:numSorts] do
    let ty := Ty.mk s false
    let (a, id) := add asserts s!"refl_{f.sortName s}" #[Node.var 0 ty] #[] (r.eq s false (v 0 ty) (v 0 ty)) #[] .refl 0
    asserts := a
    r := { r with refl := r.refl.insert s id }
    if f.sorts[s]!.isProvable then
      let (a, id) := add asserts s!"conv_{f.sortName s}" #[Node.var 0 ty, Node.var 1 ty] #[v 1 ty, r.eq s true (v 0 ty) (v 1 ty)]
        (v 0 ty) #[] .conv 0
      asserts := a
      r := { r with conv := r.conv.insert s id }
  for t in [0:base] do
    let info := terms[t]!
    let regular := (Array.range info.args.size).filter fun k => !Ty.isName info.args[k]!
    if regular.isEmpty then continue
    -- the variables: one per bound argument, two per regular one
    let mut vars : Array Nat := #[]
    let mut as : Array Exp := #[]
    let mut bs : Array Exp := #[]
    for k in [0:info.args.size] do
      let ty := info.args[k]!
      if Ty.isName ty then
        vars := vars.push (Node.var vars.size ty)
        as := as.push (Exp.ofVar vars.back!)
        bs := bs.push (Exp.ofVar vars.back!)
      else
        vars := (vars.push (Node.var vars.size ty)).push (Node.var (vars.size + 1) ty)
        as := as.push (Exp.ofVar vars[vars.size - 2]!)
        bs := bs.push (Exp.ofVar vars.back!)
    let sortOf (k : Nat) : Nat := Ty.sort info.args[k]!
    let rs := Ty.sort info.ty
    let lhs := Exp.mkApp t info.ty as
    let rhs := Exp.mkApp t info.ty bs
    let (a, id) := add asserts s!"cong_{info.name}" vars (regular.map fun k => r.eq (sortOf k) false as[k]! bs[k]!)
      (r.eq rs false lhs rhs) #[] (.cong t) termAfter[t]!
    asserts := a
    r := { r with cong := r.cong.insert t id }
    for i in regular do
      let (a, id) := add asserts s!"cong'_{info.name}_{i}" vars
        (regular.map fun k => r.eq (sortOf k) (k == i) as[k]! bs[k]!) (r.eq rs true lhs rhs) #[] (.cong t) termAfter[t]!
      asserts := a
      r := { r with congS := r.congS.insert (t, i) id }
  for t in [0:base] do
    let info := terms[t]!
    let some value := info.value | continue
    let n := info.args.size
    let m := value.dummies.size
    let xs := (Array.range n).map fun k => Node.var k info.args[k]!
    let rs := Ty.sort info.ty
    let other := Node.var (n + m) (Ty.mk rs false)
    let vars := xs ++ value.dummies ++ #[other]
    let app := Exp.mkApp t info.ty (xs.map Exp.ofVar)
    let mut disjs : Array (Nat × Nat) := #[]
    for j in [0:m] do
      for i in [0:n] do disjs := disjs.push (n + j, i)
      for j' in [j + 1:m] do disjs := disjs.push (n + j, n + j')
    for strict in [false, true] do
      let (a, id) := add asserts s!"unfold{if strict then "'" else ""}_{info.name}" vars
        #[r.eq rs false value.expr (Exp.ofVar other)] (r.eq rs strict app (Exp.ofVar other)) disjs (.unfold t) termAfter[t]!
      asserts := a
      r := if strict then { r with unfoldS := r.unfoldS.insert t id } else { r with unfold := r.unfold.insert t id }
      let (a, id) := add asserts s!"fold{if strict then "'" else ""}_{info.name}" vars
        #[r.eq rs false (Exp.ofVar other) value.expr] (r.eq rs strict (Exp.ofVar other) app) disjs (.fold t) termAfter[t]!
      asserts := a
      r := if strict then { r with foldS := r.foldS.insert t id } else { r with fold := r.fold.insert t id }
  return (terms, asserts, r)

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
  -- for each term, how many assertions are declared before it
  let mut termAfter : Array Nat := Array.replicate f.terms.size 0
  let mut nThms := 0
  for s in f.stmts do
    match s.kind with
    | .sort => nSorts := nSorts + 1
    | .termDef _ =>
      termAfter := termAfter.set! s.index nThms
      nTerms := nTerms + 1
    | _ =>
      before := before.set! s.index (nSorts, nTerms)
      nThms := nThms + 1
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
          sortsBefore := before[i]!.1, termsBefore := before[i]!.2, rank := 2 * i + 1 }
  if defs.isEmpty then return { file := f, terms, defs, asserts }
  let (terms', asserts', conv) := convRules f terms termAfter asserts
  return { file := f, terms := terms', defs, asserts := asserts', conv }

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

/-- The index of the conclusions of all assertions, each with its rank (`Assertion.rank`). -/
def index (db : Db) : Index Nat :=
  db.asserts.foldl (init := {}) fun ix a => ix.insert a.concl a.id a.rank

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
    if a.pseudo.isSome then ix
    else if a.hyps.size == 1 then { ix with single := ix.single.insert a.hyps[0]! a.id a.id }
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

end Skeleton

/-- A node of a conversion proof as the skeleton reader rebuilds it, in the orientation
`a ≡ b` of its `Conv` (the goal's side on the left); the numbers are holes. -/
inductive CNode where
  | refl
  | cong (t : Nat) (kids : Array Nat)
  | unfold (f : Nat) (kid : Nat)
  | fold (f : Nat) (kid : Nat)
  deriving Inhabited

/-- What the stack holds while a proof body is read with its expressions. -/
inductive SkItem where
  | expr (e : Exp)
  | proof (e : Exp) (sk : Skeleton)
  /-- `⊢ e1` made by `Conv`, whose conversion is still being read: slot `k`. -/
  | pending (e1 : Exp) (k : Nat)
  /-- The obligation `left =?= right` that hole `h` stands for; `flipped` if `left` is
  on the side of the proved statement, not the goal (after `Symm`). -/
  | obl (left right : Exp) (h : Nat) (flipped : Bool)
  deriving Inhabited

/-- A `Conv` being read: its hole, how many obligations are open, its sort, and the proof
converted. -/
structure SkSlot where
  root : Nat
  open_ : Nat := 1
  sort : Nat
  sk : Skeleton
  deriving Inhabited

/-- Does the conversion proof at hole `h` unfold or fold anything? -/
partial def convUnfolds (holes : Array CNode) (h : Nat) : Bool :=
  match holes[h]! with
  | .refl => false
  | .cong _ kids => kids.any (convUnfolds holes)
  | .unfold .. | .fold .. => true

/-- The conversion proof at hole `h` as a tree of conversion rules; `strict` asks for
`≡'`, whose proof has an unfolding: of a `cong`, the first argument that has one carries
it. `none` if a strict one has none. -/
partial def convSkeleton (db : Db) (holes : Array CNode) (sorts : Array Nat) (h : Nat) (strict : Bool) :
    Except String (Option Skeleton) := do
  let r := db.conv
  let refl : Except String (Option Skeleton) :=
    if strict then .ok none
    else match r.refl[sorts[h]!]? with
      | some id => .ok (some (.step id #[]))
      | none => .error "no refl for this sort"
  let rule (m : Std.HashMap Nat Nat) (t : Nat) : Except String Nat :=
    match m[t]? with
    | some id => .ok id
    | none => .error s!"no conversion rule for term {t}"
  match holes[h]! with
  | .refl => refl
  | .cong t kids =>
    let args := db.terms[t]!.args
    let regular := (Array.range args.size).filter fun k => !Ty.isName args[k]!
    -- a term with bound arguments only: the two sides are the same expression
    if regular.isEmpty || kids.size != args.size then return ← refl
    let carrier := regular.find? fun k => convUnfolds holes kids[k]!
    let id ←
      if strict then
        match carrier with
        | none => return none
        | some i =>
          match r.congS[(t, i)]? with
          | some id => pure id
          | none => throw s!"no conversion rule for term {t}"
      else rule r.cong t
    let mut children := #[]
    for k in regular do
      match ← convSkeleton db holes sorts kids[k]! (strict && some k == carrier) with
      | some c => children := children.push c
      | none => return none
    return some (.step id children)
  | .unfold f kid =>
    let id ← rule (if strict then r.unfoldS else r.unfold) f
    return (← convSkeleton db holes sorts kid false).map fun c => .step id #[c]
  | .fold f kid =>
    let id ← rule (if strict then r.foldS else r.fold) f
    return (← convSkeleton db holes sorts kid false).map fun c => .step id #[c]

/-- The skeleton of a proof body with conversions, in the conversion rules of
`convRules`: each `Conv` is a step of `conv_s` whose second child is its conversion
proof, read back from the commands — `Refl` is `refl`, `Cong` is `cong`, `Unfold` is
`unfold`, or `fold` where a `Symm` has turned the obligation round. The expressions are
tracked, because a conversion is told by them. A `Conv` with no unfolding in it changes
nothing and is left out. `ConvCut` and `ConvSave`, which share a conversion, are not
read: `none`. -/
def skeletonWithConvs (db : Db) (a : Assertion) (cmds : Array ProofCmd) : Except String (Option Skeleton) := do
  let r := db.conv
  let mut stack : Array SkItem := #[]
  let mut heap : Array SkItem := a.vars.map fun v => .expr (Exp.ofVar v)
  let mut slots : Array SkSlot := #[]
  let mut holes : Array CNode := #[]
  let mut sorts : Array Nat := #[]
  let mut hyps := 0
  let mut dummies := 0
  let popExpr (stack : Array SkItem) : Except String (Exp × Array SkItem) :=
    match stack.back? with
    | some (.expr e) => .ok (e, stack.pop)
    | _ => .error "expected an expression on the stack"
  let popObl (stack : Array SkItem) : Except String ((Exp × Exp × Nat × Bool) × Array SkItem) :=
    match stack.back? with
    | some (.obl l r h fl) => .ok ((l, r, h, fl), stack.pop)
    | _ => .error "expected an obligation on the stack"
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
      let h := holes.size
      holes := holes.push .refl
      sorts := sorts.push (Ty.sort e1.ty)
      slots := slots.push { root := h, sort := Ty.sort e1.ty, sk }
      stack := (st.push (.pending e1 (slots.size - 1))).push (.obl e1 e2 h false)
    | .refl | .cong | .unfold =>
      let (e, st) ← if c matches .unfold then popExpr stack else pure (default, stack)
      let ((l, rt, h, fl), st) ← popObl st
      stack := st
      -- the slot of the innermost pending `Conv`
      let some k := (stack.findSomeRev? fun it => match it with | .pending _ k => some k | _ => none)
        | throw "a conversion command outside a conversion"
      match c with
      | .refl =>
        holes := holes.set! h .refl
        slots := slots.modify k fun sl => { sl with open_ := sl.open_ - 1 }
      | .cong =>
        let ls := l.argStarts 0
        let rs := rt.argStarts 0
        if ls.size != rs.size then throw "Cong: the two sides differ in arity"
        let kids := (Array.range ls.size).map (holes.size + ·)
        for i in [0:ls.size] do
          holes := holes.push .refl
          sorts := sorts.push (Ty.sort (l.sub ls[i]!).ty)
        holes := holes.set! h (.cong (Node.appId l.nodes[0]!) kids)
        -- the first argument ends on top
        for j in [0:ls.size] do
          let i := ls.size - 1 - j
          stack := stack.push (.obl (l.sub ls[i]!) (rt.sub rs[i]!) kids[i]! fl)
        slots := slots.modify k fun sl => { sl with open_ := sl.open_ + ls.size - 1 }
      | _ =>
        let t := Node.appId l.nodes[0]!
        let kid := holes.size
        holes := holes.push .refl
        sorts := sorts.push sorts[h]!
        holes := holes.set! h (if fl then .fold t kid else .unfold t kid)
        stack := stack.push (.obl e rt kid fl)
      if slots[k]!.open_ == 0 then
        -- the conversion is complete: the pending proof becomes a `conv_s` step
        match stack.back? with
        | some (.pending e1 k') =>
          if k' != k then throw "the conversions are not nested"
          let slot := slots[k]!
          let sk ← match convSkeleton db holes sorts slot.root true with
            | .ok (some conv) =>
              match r.conv[slot.sort]? with
              | some id => pure (Skeleton.step id #[slot.sk, conv])
              | none => throw "Conv in a sort that is not provable"
            | .ok none => pure slot.sk
            | .error e => throw e
          stack := stack.pop.push (.proof e1 sk)
        | _ => throw "the obligations of a conversion are not above its proof"
    | .symm =>
      let ((l, rt, h, fl), st) ← popObl stack
      stack := st.push (.obl rt l h !fl)
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
