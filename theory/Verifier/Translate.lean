/-
From the machine's data to the semantics' (milestone V3, part a): bound-variable
numbers to variables, binders to `mm0.binder`, nodes of the store to `mm0.sexpr`, unify
streams to statements, and a decoded file to an `mm0.env`.
-/
import Verifier.Machine
import Mathlib.Data.Finset.Image

namespace Verifier

open mm0

/-! ### Variables and binders -/

/-- The variable of bound-variable number `k`: the `k`-th bound binder, or, past the
binders, the `k - nb`-th dummy, which is variable `bs.length + (k - nb)`. -/
def bvVar (bs : List Binder) (k : ℕ) : ℕ :=
  if h : k < (boundNumbers bs).length then (boundNumbers bs)[k] else bs.length + (k - (boundNumbers bs).length)

def Binder.toMm0 (bs : List Binder) (b : Binder) : mm0.binder :=
  if b.bound then .bound b.sort else .reg b.sort (b.deps.image (bvVar bs))

/-- The context of a declaration with binders `bs` and dummies of sorts `ds`. -/
def ctxOf (bs : List Binder) (ds : List ℕ) : mm0.ctx :=
  bs.map (Binder.toMm0 bs) ++ ds.map mm0.binder.bound

def depTypeOf (bs : List Binder) (ret : Binder) : mm0.dep_type :=
  (ret.sort, ret.deps.image (bvVar bs))

/-! ### Nodes -/

/-- The expression of node `p`, with fuel: a node's arguments are earlier nodes. -/
def toSexprF (store : List Node) : ℕ → ℕ → sexpr
  | 0, _ => sexpr.var 0
  | fuel + 1, p =>
    match store[p]? with
    | some (.var _ v) => sexpr.var v
    | some (.app _ t args) => sexpr.app t (args.map (toSexprF store fuel))
    | none => sexpr.var 0

def toSexpr (store : List Node) (p : ℕ) : sexpr := toSexprF store (p + 1) p

/-- A store whose applications point at earlier nodes. -/
def StoreWF (store : List Node) : Prop :=
  ∀ p ty t args, store[p]? = some (Node.app ty t args) → ∀ q ∈ args, q < p

theorem toSexprF_stable {store : List Node} (hwf : StoreWF store) :
    ∀ (fuel : ℕ) (p : ℕ), p < fuel → toSexprF store fuel p = toSexpr store p
  | 0, p, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, p, h => by
    unfold toSexpr
    conv_rhs => unfold toSexprF
    unfold toSexprF
    cases hp : store[p]? with
    | none => rfl
    | some n =>
      cases n with
      | var _ _ => rfl
      | app ty t args =>
        simp only
        congr 1
        apply List.map_congr_left
        intro q hq
        have hqp := hwf p ty t args hp q hq
        rw [toSexprF_stable hwf fuel q (by omega), toSexprF_stable hwf p q hqp]

theorem toSexpr_var {store : List Node} {p : ℕ} {ty : Ty} {v : ℕ} (h : store[p]? = some (Node.var ty v)) :
    toSexpr store p = sexpr.var v := by
  unfold toSexpr toSexprF
  simp [h]

theorem toSexpr_app {store : List Node} (hwf : StoreWF store) {p : ℕ} {ty : Ty} {t : ℕ} {args : List ℕ}
    (h : store[p]? = some (Node.app ty t args)) :
    toSexpr store p = sexpr.app t (args.map (toSexpr store)) := by
  unfold toSexpr
  conv_lhs => unfold toSexprF
  simp only [h]
  congr 1
  apply List.map_congr_left
  intro q hq
  exact toSexprF_stable hwf p q (hwf p ty t args h q hq)

/-- A longer store gives the same expressions for the nodes it has. -/
theorem toSexprF_append {store : List Node} (hwf : StoreWF store) (n : Node) :
    ∀ (fuel p : ℕ), p < store.length → toSexprF (store ++ [n]) fuel p = toSexprF store fuel p
  | 0, _, _ => rfl
  | fuel + 1, p, hp => by
    unfold toSexprF
    rw [List.getElem?_append_left hp]
    cases hq : store[p]? with
    | none => rfl
    | some m =>
      cases m with
      | var _ _ => rfl
      | app ty t args =>
        simp only
        congr 1
        apply List.map_congr_left
        intro q hq'
        exact toSexprF_append hwf n fuel q (lt_trans (hwf p ty t args hq q hq') hp)

theorem toSexpr_append {store : List Node} (hwf : StoreWF store) (n : Node) {p : ℕ} (hp : p < store.length) :
    toSexpr (store ++ [n]) p = toSexpr store p :=
  toSexprF_append hwf n (p + 1) p hp

theorem StoreWF.append_var {store : List Node} (hwf : StoreWF store) (ty : Ty) (v : ℕ) :
    StoreWF (store ++ [Node.var ty v]) := by
  intro p ty' t args hp q hq
  by_cases h : p < store.length
  · rw [List.getElem?_append_left h] at hp
    exact hwf p ty' t args hp q hq
  · rw [List.getElem?_append_right (Nat.le_of_not_lt h)] at hp
    cases hpl : p - store.length with
    | zero => rw [hpl] at hp; simp at hp
    | succ k => rw [hpl] at hp; simp at hp

theorem StoreWF.append_app {store : List Node} (hwf : StoreWF store) (ty : Ty) (t : ℕ) {args : List ℕ}
    (hargs : ∀ q ∈ args, q < store.length) : StoreWF (store ++ [Node.app ty t args]) := by
  intro p ty' t' args' hp q hq
  by_cases h : p < store.length
  · rw [List.getElem?_append_left h] at hp
    exact hwf p ty' t' args' hp q hq
  · rw [List.getElem?_append_right (Nat.le_of_not_lt h)] at hp
    cases hpl : p - store.length with
    | zero =>
      rw [hpl] at hp
      simp only [List.getElem?_cons_zero, Option.some.injEq, Node.app.injEq] at hp
      obtain ⟨_, _, rfl⟩ := hp
      have := hargs q hq
      omega
    | succ k => rw [hpl] at hp; simp at hp

/-! ### Unify streams -/

open Whitehead.Mmb (UnifyCmd)

/-- The variables of the arguments, the initial heap of a stream. -/
def initHeap (n : ℕ) : List sexpr := (List.range n).map sexpr.var

mutual
/-- The meaning of a unify stream, read left to right: the expression it starts with,
the rest of the stream, the heap after it (the arguments' variables, then one entry per
saved term and dummy, in stream order) and the sorts of the dummies so far. A saved
term takes its heap entry before its arguments are read (as `Unify.term` does), with a
placeholder meanwhile; a dummy is the next variable after the arguments. -/
def decodeExpr (terms : List TermDecl) (nargs : ℕ) :
    ℕ → List UnifyCmd → List sexpr → List ℕ → Option (sexpr × List UnifyCmd × List sexpr × List ℕ)
  | 0, _, _, _ => none
  | fuel + 1, us, heap, ds =>
    match us with
    | UnifyCmd.ref i :: rest => (heap[i]?).map fun e => (e, rest, heap, ds)
    | UnifyCmd.term t save :: rest =>
      match terms[t]? with
      | none => none
      | some decl =>
        let heap' := if save then heap ++ [sexpr.var 0] else heap
        match decodeN terms nargs fuel decl.args.length rest heap' ds with
        | none => none
        | some (args, rest', heap'', ds') =>
          some (sexpr.app t args, rest', if save then heap''.set heap.length (sexpr.app t args) else heap'', ds')
    | UnifyCmd.dummy s :: rest =>
      some (sexpr.var (nargs + ds.length), rest, heap ++ [sexpr.var (nargs + ds.length)], ds ++ [s])
    | _ => none

/-- `n` expressions in sequence. -/
def decodeN (terms : List TermDecl) (nargs : ℕ) :
    ℕ → ℕ → List UnifyCmd → List sexpr → List ℕ → Option (List sexpr × List UnifyCmd × List sexpr × List ℕ)
  | 0, _, _, _, _ => none
  | _ + 1, 0, us, heap, ds => some ([], us, heap, ds)
  | fuel + 1, n + 1, us, heap, ds =>
    match decodeExpr terms nargs fuel us heap ds with
    | none => none
    | some (e, rest, heap', ds') =>
      match decodeN terms nargs fuel n rest heap' ds' with
      | none => none
      | some (es, rest', heap'', ds'') => some (e :: es, rest', heap'', ds'')
end

/-- The hypotheses of a theorem's stream: `UHyp` and an expression, each. -/
def decodeHyps (terms : List TermDecl) (nargs : ℕ) :
    ℕ → List UnifyCmd → List sexpr → List ℕ → Option (List sexpr)
  | 0, _, _, _ => none
  | _ + 1, [], _, _ => some []
  | fuel + 1, UnifyCmd.hyp :: rest, heap, ds =>
    match decodeExpr terms nargs fuel rest heap ds with
    | none => none
    | some (h, rest', heap', ds') => (decodeHyps terms nargs fuel rest' heap' ds').map (h :: ·)
  | _ + 1, _, _, _ => none

/-- The statement of a theorem's stream: its conclusion and its hypotheses, over the
theorem's binders. -/
def decodeThm (terms : List TermDecl) (nargs : ℕ) (us : List UnifyCmd) : Option (sexpr × List sexpr) :=
  match decodeExpr terms nargs (us.length + 1) us (initHeap nargs) [] with
  | none => none
  | some (concl, rest, heap, ds) => (decodeHyps terms nargs (rest.length + 1) rest heap ds).map fun hs => (concl, hs)

/-- The value of a def's stream, over its binders and then its dummies, with the
dummies' sorts. -/
def decodeDef (terms : List TermDecl) (nargs : ℕ) (us : List UnifyCmd) : Option (sexpr × List ℕ) :=
  match decodeExpr terms nargs (us.length + 1) us (initHeap nargs) [] with
  | some (v, [], _, ds) => some (v, ds)
  | _ => none

/-! ### The environment of a file -/

def termDeclOf (f : File) (t : ℕ) : Option mm0.decl :=
  (f.terms[t]?).bind fun d =>
    let args := d.args.map (Binder.toMm0 d.args)
    match d.defn with
    | none => some (decl.term t args (depTypeOf d.args d.ret))
    | some us => (decodeDef f.terms d.args.length us).map fun vd =>
        decl.defn t args (depTypeOf d.args d.ret) (some (vd.2, vd.1))

def thmDeclOf (f : File) (isAx : Bool) (h : ℕ) : Option mm0.decl :=
  (f.thms[h]?).bind fun d =>
    (decodeThm f.terms d.args.length d.unify).map fun ch =>
      let args := d.args.map (Binder.toMm0 d.args)
      if isAx then decl.ax args ch.2 ch.1 else decl.thm args ch.2 ch.1

/-- The declarations of the statements, in order, with the three counters. -/
def toEnvAux (f : File) : List Stmt → ℕ → ℕ → ℕ → Option mm0.env
  | [], _, _, _ => some []
  | s :: ss, ns, nt, nh =>
    match s.kind with
    | .sort => do
      let sd ← f.sorts[ns]?
      let E ← toEnvAux f ss (ns + 1) nt nh
      pure (decl.sort ns sd :: E)
    | .term => do
      let d ← termDeclOf f nt
      let E ← toEnvAux f ss ns (nt + 1) nh
      pure (d :: E)
    | .defn _ => do
      let d ← termDeclOf f nt
      let E ← toEnvAux f ss ns (nt + 1) nh
      pure (d :: E)
    | .ax => do
      let d ← thmDeclOf f true nh
      let E ← toEnvAux f ss ns nt (nh + 1)
      pure (d :: E)
    | .thm _ => do
      let d ← thmDeclOf f false nh
      let E ← toEnvAux f ss ns nt (nh + 1)
      pure (d :: E)

/-- The environment a file declares, when its streams decode. -/
def toEnv (f : File) : Option mm0.env := toEnvAux f f.stmts 0 0 0

end Verifier
