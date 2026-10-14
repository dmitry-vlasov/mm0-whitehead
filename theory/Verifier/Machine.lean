/-
The stack machine of `.mmb` proof files, as relations: `mm0b.lean` of the MM0
repository completed by the checks of `docs/MMB-NOTES.md`, section 6 (milestone V2 of
`docs/VERIFIER-THEORY.md`). The input is a decoded file: the reader's commands
(`Whitehead.Mmb.ProofCmd`, `UnifyCmd`), the binders as records, the sorts as the
semantics' `sort_data`. Each rule names the paragraph of the notes it implements.

The representation is the semantics', not the fast verifier's: a node carries its sort,
whether it is a bound variable, and the set of bound variables it depends on, as
numbers; the store, stack and heap are lists; equality of expressions is identity of
nodes, as in the format.
-/
import Spec.Mm0
import Mathlib.Data.Finset.Union
import Whitehead.Mmb.Types

namespace Verifier

open Whitehead.Mmb (ProofCmd UnifyCmd)

/-! ### The decoded file -/

/-- A binder, or a return type: the `arg` word decoded (notes, section 2). `deps` are
bound-variable numbers: the `k`-th bound variable of the declaration, binders and
dummies together, is number `k`. -/
structure Binder where
  sort : ℕ
  bound : Bool
  deps : Finset ℕ
  deriving DecidableEq

structure TermDecl where
  args : List Binder
  ret : Binder
  /-- The unify stream of the value, for a def. -/
  defn : Option (List UnifyCmd)

structure ThmDecl where
  args : List Binder
  unify : List UnifyCmd

inductive StmtKind
  | sort
  | term
  | defn (isLocal : Bool)
  | ax
  | thm (isLocal : Bool)
  deriving DecidableEq

structure Stmt where
  kind : StmtKind
  /-- The proof body, without its `END`; empty for a sort or a term. -/
  body : List ProofCmd

structure File where
  sorts : List mm0.sort_data
  terms : List TermDecl
  thms : List ThmDecl
  stmts : List Stmt

/-- The limit of the format: bound variables are bits 0 to 54 of a word (section 9,
point 10). -/
def maxBound : ℕ := 55

/-! ### The machine -/

/-- The type of a node: its sort, whether it is a bound variable, and the bound
variables it depends on (notes, "Machine state"). -/
structure Ty where
  sort : ℕ
  bound : Bool
  deps : Finset ℕ
  deriving DecidableEq

def Ty.ofBinder (b : Binder) : Ty := ⟨b.sort, b.bound, b.deps⟩

/-- A node of the store: a variable (its number among the declaration's variables,
binders then dummies), or an application. -/
inductive Node
  | var (ty : Ty) (v : ℕ)
  | app (ty : Ty) (t : ℕ) (args : List ℕ)

def Node.ty : Node → Ty
  | .var ty _ => ty
  | .app ty _ _ => ty

/-- An element of the stack or the heap: `expr e`, `proof e` (`⊢ e`), a conversion
`e1 = e2`, an obligation `e1 =?= e2` (never on the heap). -/
inductive El
  | expr (e : ℕ)
  | proof (e : ℕ)
  | conv (e1 e2 : ℕ)
  | coConv (e1 e2 : ℕ)
  deriving DecidableEq

structure State where
  store : List Node
  stack : List El
  heap : List El
  /-- The hypotheses declared so far, in order. -/
  hyps : List ℕ
  /-- How many bound variables exist: the next dummy gets this number. -/
  nextBv : ℕ
  /-- How many variables exist: the next dummy gets this number. -/
  nextVar : ℕ

/-- What a statement is checked against: the sorts, terms and theorems declared before
it, and whether it is a definition. -/
structure Ctx where
  sorts : List mm0.sort_data
  terms : List TermDecl
  thms : List ThmDecl
  isDef : Bool

/-- The type of node `e`. -/
def State.ty (st : State) (e : ℕ) : Option Ty := (st.store[e]?).map Node.ty

/-- The arguments of an application: `n` expressions popped, the first on top. -/
inductive popArgs : ℕ → List El → List ℕ → List El → Prop
  | zero (S) : popArgs 0 S [] S
  | succ (n S₁ p ps S₂) : popArgs n S₁ ps S₂ → popArgs (n + 1) (El.expr p :: S₁) (ps ++ [p]) S₂

/-- The arguments against the binders (notes, `Term`): the sorts are equal, and a bound
binder takes a bound variable. -/
def argsOk (st : State) : List Binder → List ℕ → Prop
  | [], [] => True
  | b :: bs, p :: ps => (∃ ty, st.ty p = some ty ∧ ty.sort = b.sort ∧ (b.bound → ty.bound)) ∧ argsOk st bs ps
  | _, _ => False

/-- The positions of the bound binders among `bs`, in order: bound-variable number `k`
of the declaration is the binder at position `(boundNumbers bs)[k]`. (The binders'
`deps` are over these numbers.) -/
def boundNumbers (bs : List Binder) : List ℕ :=
  (List.range bs.length).filter fun i => (bs[i]?.map (·.bound)) = some true

/-- The variable of bound-variable number `k`: the `k`-th bound binder, or, past the
binders, the `k - nb`-th dummy, which is variable `bs.length + (k - nb)`. -/
def bvVar (bs : List Binder) (k : ℕ) : ℕ :=
  if h : k < (boundNumbers bs).length then (boundNumbers bs)[k] else bs.length + (k - (boundNumbers bs).length)

/-- The dependencies of the argument at the position of bound-variable number `k`. -/
def argDeps (bs : List Binder) (tys : List Ty) (k : ℕ) : Finset ℕ := (tys[bvVar bs k]?.map fun ty : Ty => ty.deps).getD ∅

/-- The dependencies of an application (notes, `Term`): in an axiom or theorem the
union over the arguments; in a definition the free variables — of a regular argument,
its dependencies less those of the bound arguments its binder depends on; of a bound
argument, its dependencies if the return type depends on it. -/
def appDeps (isDef : Bool) (bs : List Binder) (ret : Binder) (tys : List Ty) : Finset ℕ :=
  if isDef then
    ((List.range bs.length).filter fun i => (bs[i]?.map (·.bound)) = some false).foldr (init := ∅) (fun i acc =>
      acc ∪ (((tys[i]?.map fun ty : Ty => ty.deps).getD ∅) \
        ((bs[i]?.map fun b : Binder => b.deps).getD ∅).biUnion (argDeps bs tys))) ∪
    ret.deps.biUnion (argDeps bs tys)
  else
    tys.foldr (init := ∅) fun ty acc => acc ∪ ty.deps

/-- The disjointness conditions of `Thm` (notes, `Thm`): a bound argument's dependency
set is disjoint from every earlier argument's; a regular argument's is disjoint from the
set of every bound binder seen so far that its binder does not depend on. `seen` are the
bound binders so far with the sets of their arguments. -/
def thmDisjoint (st : State) : List Binder → List ℕ → List (ℕ × Finset ℕ) → List (Finset ℕ) → Prop
  | [], [], _, _ => True
  | b :: bs, p :: ps, seen, earlier =>
    (∃ ty, st.ty p = some ty ∧
      (if b.bound then
        (∀ d ∈ earlier, Disjoint ty.deps d) ∧ thmDisjoint st bs ps (seen ++ [(seen.length, ty.deps)]) (earlier ++ [ty.deps])
      else
        (∀ jd ∈ seen, jd.1 ∉ b.deps → Disjoint ty.deps jd.2) ∧ thmDisjoint st bs ps seen (earlier ++ [ty.deps])))
  | _, _, _, _ => False

/-- The modes of the unifier (notes, "Unify commands"). -/
inductive UMode
  | thm
  | defn
  | thmEnd
  deriving DecidableEq

/-- The unify heap: the substitution, then the saved terms (marked) and the dummies. -/
abbrev UHeap := List (ℕ × Bool)

/-- The unifier: `Unify c mode st (H, us) K S S'` — with the main stack `S` before and
`S'` after, the unify stack `K`, the unify heap `H`, and the hypotheses `hs` still to be
used (`UThmEnd`). -/
inductive Unify (c : Ctx) (st : State) : UMode → UHeap → List UnifyCmd → List ℕ → List El → List ℕ → List El → List ℕ → Prop
  | ref (mode H us e K S hs S' hs') (i : ℕ) (b : Bool) :
    H[i]? = some (e, b) →
    Unify c st mode H us K S hs S' hs' →
    Unify c st mode H (UnifyCmd.ref i :: us) (e :: K) S hs S' hs'
  | term (mode H us e t save ty args K S hs S' hs') :
    st.store[e]? = some (Node.app ty t args) →
    Unify c st mode (if save then H ++ [(e, true)] else H) us (args ++ K) S hs S' hs' →
    Unify c st mode H (UnifyCmd.term t save :: us) (e :: K) S hs S' hs'
  | dummy (H us e s ty v K S hs S' hs') :
    st.store[e]? = some (Node.var ty v) → ty.bound = true → ty.sort = s →
    (∀ h ∈ H, h.2 = false → ∀ ty', st.ty h.1 = some ty' → Disjoint ty.deps ty'.deps) →
    Unify c st .defn (H ++ [(e, false)]) us K S hs S' hs' →
    Unify c st .defn H (UnifyCmd.dummy s :: us) (e :: K) S hs S' hs'
  -- the unify stack is empty at a hypothesis: the conclusion has been read
  -- (`mm0b.lean` lets a hypothesis come at any point; the streams of the format do not)
  | hyp_thm (H us e S hs S' hs') :
    Unify c st .thm H us [e] S hs S' hs' →
    Unify c st .thm H (UnifyCmd.hyp :: us) [] (El.proof e :: S) hs S' hs'
  | hyp_end (H us e S hs S' hs') :
    Unify c st .thmEnd H us [e] S hs S' hs' →
    Unify c st .thmEnd H (UnifyCmd.hyp :: us) [] S (hs ++ [e]) S' hs'
  | nil (mode H S hs) : (mode = .thmEnd → hs = []) → Unify c st mode H [] [] S hs S hs

/-- A step of the machine on a proof command (notes, "Proof commands"). -/
inductive Step (c : Ctx) : ProofCmd → State → State → Prop
  | term (st t save decl args S' ty) :
    c.terms[t]? = some decl →
    popArgs decl.args.length st.stack args S' →
    argsOk st decl.args args →
    ty = ⟨decl.ret.sort, false, appDeps c.isDef decl.args decl.ret (args.map fun p => (st.ty p).getD ⟨0, false, ∅⟩)⟩ →
    Step c (ProofCmd.term t save)
      st { st with stack := El.expr st.store.length :: S',
                   heap := if save then st.heap ++ [El.expr st.store.length] else st.heap,
                   store := st.store ++ [Node.app ty t args] }
  | ref_el (st i el) :
    st.heap[i]? = some el → (∀ e1 e2, el ≠ El.conv e1 e2) →
    Step c (ProofCmd.ref i) st { st with stack := el :: st.stack }
  | ref_conv (st i e1 e2 S) :
    st.heap[i]? = some (El.conv e1 e2) → st.stack = El.coConv e1 e2 :: S →
    Step c (ProofCmd.ref i) st { st with stack := S }
  | dummy (st s sd) :
    c.sorts[s]? = some sd → sd.strict = false → sd.free = false → st.nextBv < maxBound →
    Step c (ProofCmd.dummy s) st
      { st with stack := El.expr st.store.length :: st.stack,
                heap := st.heap ++ [El.expr st.store.length],
                store := st.store ++ [Node.var ⟨s, true, {st.nextBv}⟩ st.nextVar],
                nextBv := st.nextBv + 1, nextVar := st.nextVar + 1 }
  | thm (st t save decl e args S₁ S₂) :
    c.isDef = false →
    c.thms[t]? = some decl →
    st.stack = El.expr e :: S₁ →
    popArgs decl.args.length S₁ args (S₂) →
    argsOk st decl.args args →
    thmDisjoint st decl.args args [] [] →
    ∀ S₃, Unify c st .thm (args.map fun p => (p, false)) decl.unify [e] S₂ [] S₃ [] →
    Step c (ProofCmd.thm t save) st
      { st with stack := El.proof e :: S₃, heap := if save then st.heap ++ [El.proof e] else st.heap }
  | hyp (st e S ty sd) :
    c.isDef = false → st.stack = El.expr e :: S → st.ty e = some ty →
    c.sorts[ty.sort]? = some sd → sd.provable = true →
    Step c ProofCmd.hyp st { st with stack := El.proof e :: S, heap := st.heap ++ [El.proof e], hyps := st.hyps ++ [e] }
  | conv (st e1 e2 S) :
    st.stack = El.proof e2 :: El.expr e1 :: S →
    Step c ProofCmd.conv st { st with stack := El.coConv e1 e2 :: El.proof e1 :: S }
  | refl (st e S) :
    st.stack = El.coConv e e :: S →
    Step c ProofCmd.refl st { st with stack := S }
  | symm (st e1 e2 S) :
    st.stack = El.coConv e1 e2 :: S →
    Step c ProofCmd.symm st { st with stack := El.coConv e2 e1 :: S }
  | cong (st e1 e2 S ty1 ty2 t args1 args2) :
    st.stack = El.coConv e1 e2 :: S →
    st.store[e1]? = some (Node.app ty1 t args1) → st.store[e2]? = some (Node.app ty2 t args2) →
    args1.length = args2.length →
    Step c ProofCmd.cong st { st with stack := List.zipWith El.coConv args1 args2 ++ S }
  | unfold (st e e' t ty args decl us S) (e2 : ℕ) :
    st.stack = El.expr e2 :: El.coConv e e' :: S →
    st.store[e]? = some (Node.app ty t args) →
    c.terms[t]? = some decl → decl.defn = some us →
    Unify c st .defn (args.map fun p => (p, false)) us [e2] S [] S [] →
    Step c ProofCmd.unfold st { st with stack := El.coConv e2 e' :: S }
  | convCut (st e1 e2 S) :
    st.stack = El.coConv e1 e2 :: S →
    Step c ProofCmd.convCut st { st with stack := El.coConv e1 e2 :: El.conv e1 e2 :: S }
  | convSave (st e1 e2 S) :
    st.stack = El.conv e1 e2 :: S →
    Step c ProofCmd.convSave st { st with stack := S, heap := st.heap ++ [El.conv e1 e2] }
  | save (st el S) :
    st.stack = el :: S → (∀ e1 e2, el ≠ El.coConv e1 e2) →
    Step c ProofCmd.save st { st with heap := st.heap ++ [el] }

/-- A proof body run to its end. -/
inductive Run (c : Ctx) : List ProofCmd → State → State → Prop
  | nil (st) : Run c [] st st
  | cons (p ps st st' st'') : Step c p st st' → Run c ps st' st'' → Run c (p :: ps) st st''

/-! ### Statements -/

/-- The binders of a declaration loaded on the heap (notes, "Machine state"; `loadArgs`
of the fast verifier): a bound variable has a sort declared and not strict, and the next
number as its only dependency; a regular variable depends on bound variables declared
before it. -/
inductive LoadArgs (c : Ctx) : List Binder → State → State → Prop
  | nil (st) : LoadArgs c [] st st
  | bound (b bs st st' sd) :
    b.bound = true → c.sorts[b.sort]? = some sd → sd.strict = false → st.nextBv < maxBound →
    b.deps = {st.nextBv} →
    LoadArgs c bs { st with store := st.store ++ [Node.var (Ty.ofBinder b) st.nextVar],
                            heap := st.heap ++ [El.expr st.store.length],
                            nextBv := st.nextBv + 1, nextVar := st.nextVar + 1 } st' →
    LoadArgs c (b :: bs) st st'
  | reg (b bs st st') :
    b.bound = false → b.sort < c.sorts.length → (∀ j ∈ b.deps, j < st.nextBv) →
    LoadArgs c bs { st with store := st.store ++ [Node.var (Ty.ofBinder b) st.nextVar],
                            heap := st.heap ++ [El.expr st.store.length],
                            nextVar := st.nextVar + 1 } st' →
    LoadArgs c (b :: bs) st st'

def State.empty : State := ⟨[], [], [], [], 0, 0⟩

/-- The first `n` heap entries as the unify heap. -/
def argsUheap (st : State) (n : ℕ) : UHeap :=
  (List.range n).filterMap fun i => match st.heap[i]? with
    | some (El.expr e) => some (e, false)
    | _ => none

/-- A `Term`, `Def` or `LocalDef` statement (notes, "End of a statement"). -/
def TermOk (c : Ctx) (decl : TermDecl) (isLocal : Bool) (body : List ProofCmd) : Prop :=
  (isLocal = true → decl.defn.isSome) ∧
  ∃ st, LoadArgs c decl.args State.empty st ∧
    decl.ret.bound = false ∧
    (∃ sd, c.sorts[decl.ret.sort]? = some sd ∧ sd.pure = false) ∧
    (∀ j ∈ decl.ret.deps, j < st.nextBv) ∧
    match decl.defn with
    | none => body = []
    | some us => ∃ st' e ty, Run { c with isDef := true } body st st' ∧ st'.stack = [El.expr e] ∧
        st'.ty e = some ty ∧ ty.sort = decl.ret.sort ∧ ty.deps ⊆ decl.ret.deps ∧
        Unify { c with isDef := true } st' .defn (argsUheap st' decl.args.length) us [e] [] [] [] []

/-- An `Axiom`, `Thm` or `LocalThm` statement. -/
def ThmOk (c : Ctx) (decl : ThmDecl) (isAxiom : Bool) (body : List ProofCmd) : Prop :=
  ∃ st st' e ty sd, LoadArgs c decl.args State.empty st ∧
    Run { c with isDef := false } body st st' ∧
    st'.stack = [if isAxiom then El.expr e else El.proof e] ∧
    st'.ty e = some ty ∧ c.sorts[ty.sort]? = some sd ∧ sd.provable = true ∧
    Unify { c with isDef := false } st' .thmEnd (argsUheap st' decl.args.length) decl.unify [e] [] st'.hyps [] []

/-- The statements of a file in order, each against what is declared before it; the
counters at the end are the tables' sizes. -/
inductive Stmts (f : File) : List Stmt → ℕ → ℕ → ℕ → Prop
  | nil : Stmts f [] f.sorts.length f.terms.length f.thms.length
  | sort (ss ns nt nh) : ns < f.sorts.length → Stmts f ss (ns + 1) nt nh →
    Stmts f ({ kind := .sort, body := [] } :: ss) ns nt nh
  | term (ss ns nt nh decl) : f.terms[nt]? = some decl → decl.defn = none →
    TermOk ⟨f.sorts.take ns, f.terms.take nt, f.thms.take nh, false⟩ decl false [] →
    Stmts f ss ns (nt + 1) nh →
    Stmts f ({ kind := .term, body := [] } :: ss) ns nt nh
  | defn (ss ns nt nh decl isLocal body) : f.terms[nt]? = some decl → decl.defn.isSome →
    TermOk ⟨f.sorts.take ns, f.terms.take nt, f.thms.take nh, true⟩ decl isLocal body →
    Stmts f ss ns (nt + 1) nh →
    Stmts f ({ kind := .defn isLocal, body := body } :: ss) ns nt nh
  | ax (ss ns nt nh decl body) : f.thms[nh]? = some decl →
    ThmOk ⟨f.sorts.take ns, f.terms.take nt, f.thms.take nh, false⟩ decl true body →
    Stmts f ss ns nt (nh + 1) →
    Stmts f ({ kind := .ax, body := body } :: ss) ns nt nh
  | thm (ss ns nt nh decl isLocal body) : f.thms[nh]? = some decl →
    ThmOk ⟨f.sorts.take ns, f.terms.take nt, f.thms.take nh, false⟩ decl false body →
    Stmts f ss ns nt (nh + 1) →
    Stmts f ({ kind := .thm isLocal, body := body } :: ss) ns nt nh

/-- A proof file the machine accepts. -/
def FileOk (f : File) : Prop := Stmts f f.stmts 0 0 0

end Verifier
