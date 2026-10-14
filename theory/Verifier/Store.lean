/-
The meaning of a node's type word (milestone V3, part b): its sort is the expression's
sort, it is marked bound exactly when it is a bound variable, and its dependencies are
the bound variables the expression has (`has_var`, in an axiom or theorem) or has free
(`free`, in a definition). With the environment holding what the tables declare
(`EnvHas`), the dependency formulas of `Machine.lean` are these sets.
-/
import Verifier.Vars
import Verifier.Sexpr

namespace Verifier

open mm0

/-! ### Binders well-formed -/

/-- What `LoadArgs` establishes of the binders: a bound binder's dependency set is its
own number, a regular binder depends on bound binders before it. -/
def BindersWF (bs : List Binder) : Prop :=
  ∀ i b, bs[i]? = some b →
    (b.bound = true → b.deps = {countBefore bs i}) ∧ (b.bound = false → ∀ k ∈ b.deps, k < countBefore bs i)

/-! ### The environment and the tables -/

/-- The environment a statement is checked in has the declarations of the context's
tables, and no other term declarations. `terms` is the whole term table, for the
decoder's arities. -/
structure EnvHas (E : env) (c : Ctx) (allTerms : List TermDecl) : Prop where
  sorts : ∀ s sd, c.sorts[s]? = some sd → E.get_sd s sd
  sorts_unique : ∀ s sd, E.get_sd s sd → c.sorts[s]? = some sd
  terms : ∀ (t : ℕ) (d : TermDecl), c.terms[t]? = some d →
    ∃ o, E.get_term t (d.args.map (Binder.toMm0 d.args)) (depTypeOf d.args d.ret) o ∧
      ∀ us, d.defn = some us → ∃ v ds, decodeDef allTerms d.args.length us = some (v, ds) ∧ o = some (ds, v)
  terms_unique : ∀ t a r o, E.get_term t a r o →
    ∃ d : TermDecl, c.terms[t]? = some d ∧ a = d.args.map (Binder.toMm0 d.args) ∧ r = depTypeOf d.args d.ret
  thms : ∀ (h : ℕ) (d : ThmDecl), c.thms[h]? = some d →
    ∃ concl hs, decodeThm allTerms d.args.length d.unify = some (concl, hs) ∧
    E.get_thm (d.args.map (Binder.toMm0 d.args)) hs concl
  /-- The table is a prefix of the whole one. -/
  terms_prefix : ∀ (t : ℕ) (d : TermDecl), c.terms[t]? = some d → allTerms[t]? = some d
  /-- The declarations are well-formed: their binders, and the return type's
  dependencies among their bound binders. -/
  terms_wf : ∀ (t : ℕ) (d : TermDecl), c.terms[t]? = some d →
    BindersWF d.args ∧ ∀ m ∈ d.ret.deps, m < (boundNumbers d.args).length
  /-- A def's value is well-typed over its binders and dummies, at its result sort. -/
  defs_ok : ∀ (t : ℕ) (d : TermDecl) (us : List Whitehead.Mmb.UnifyCmd) (v : sexpr) (ds : List ℕ),
    c.terms[t]? = some d → d.defn = some us → decodeDef allTerms d.args.length us = some (v, ds) →
    sexpr.ok E (ctxOf d.args ds) v d.ret.sort

/-! ### The type word -/

/-- The number of bound variables of a statement with binders `bs` and `ds` dummies. -/
def nbv (bs : List Binder) (ds : List ℕ) : ℕ := (boundNumbers bs).length + ds.length

/-- The dependency a type word claims for bound-variable number `k`: the expression
has the variable, or has it free in a definition. -/
def Dep (E : env) (bs : List Binder) (ds : List ℕ) (isDef : Bool) (e : sexpr) (k : ℕ) : Prop :=
  if isDef then sexpr.free E (ctxOf bs ds) e (bvVar bs k) else sexpr.has_var (ctxOf bs ds) e (bvVar bs k)

structure NodeOk (E : env) (bs : List Binder) (ds : List ℕ) (isDef : Bool) (store : List Node) (p : ℕ) (n : Node) :
    Prop where
  ok : sexpr.ok E (ctxOf bs ds) (toSexpr store p) n.ty.sort
  bound : n.ty.bound = true ↔ ∃ v s, n = Node.var n.ty v ∧ (ctxOf bs ds)[v]? = some (binder.bound s)
  deps : ∀ k, k ∈ n.ty.deps ↔ k < nbv bs ds ∧ Dep E bs ds isDef (toSexpr store p) k

structure StoreOk (E : env) (bs : List Binder) (ds : List ℕ) (isDef : Bool) (store : List Node) : Prop where
  wf : StoreWF store
  nodes : ∀ p n, store[p]? = some n → NodeOk E bs ds isDef store p n

theorem NodeOk.varsLt {E : env} {bs : List Binder} {ds : List ℕ} {isDef : Bool} {store : List Node} {p : ℕ} {n : Node}
    (h : NodeOk E bs ds isDef store p n) : sexpr.VarsLt (toSexpr store p) (bs.length + ds.length) := by
  have := ok'_varsLt h.ok
  rwa [ctxOf_length] at this

/-! ### Membership in the dependency formulas -/

theorem mem_foldr_union {α : Type} [DecidableEq ℕ] (f : α → Finset ℕ) :
    ∀ (l : List α) (k : ℕ), k ∈ l.foldr (fun x acc => acc ∪ f x) ∅ ↔ ∃ x ∈ l, k ∈ f x
  | [], k => by simp
  | x :: l, k => by
    simp only [List.foldr_cons, Finset.mem_union, List.mem_cons, exists_eq_or_imp]
    rw [mem_foldr_union f l]
    exact or_comm

theorem mem_appDeps_thm (bs : List Binder) (ret : Binder) (tys : List Ty) (k : ℕ) :
    k ∈ appDeps false bs ret tys ↔ ∃ ty ∈ tys, k ∈ ty.deps := by
  unfold appDeps
  simp only [Bool.false_eq_true, ite_false]
  exact mem_foldr_union _ tys k

theorem not_isBoundAt_iff {bs : List Binder} {i : ℕ} (hi : i < bs.length) :
    ¬ isBoundAt bs i ↔ (bs[i]?.map fun b : Binder => b.bound) = some false := by
  unfold isBoundAt
  rw [List.getElem?_eq_getElem hi]
  simp only [Option.map_some, Option.some.injEq]
  cases bs[i].bound <;> simp

theorem mem_appDeps_def (bs : List Binder) (ret : Binder) (tys : List Ty) (k : ℕ) :
    k ∈ appDeps true bs ret tys ↔
      (∃ i, i < bs.length ∧ ¬ isBoundAt bs i ∧ k ∈ (tys[i]?.map fun ty : Ty => ty.deps).getD ∅ ∧
        ∀ m ∈ (bs[i]?.map fun b : Binder => b.deps).getD ∅, k ∉ argDeps bs tys m) ∨
      ∃ m ∈ ret.deps, k ∈ argDeps bs tys m := by
  unfold appDeps
  simp only [ite_true, Finset.mem_union, Finset.mem_biUnion]
  rw [mem_foldr_union]
  simp only [List.mem_filter, List.mem_range, Finset.mem_sdiff, Finset.mem_biUnion, not_exists, not_and,
    decide_eq_true_eq]
  constructor
  · rintro (⟨i, ⟨hi, hreg⟩, hk, hnot⟩ | h)
    · left
      exact ⟨i, hi, (not_isBoundAt_iff hi).2 hreg, hk, hnot⟩
    · right; exact h
  · rintro (⟨i, hi, hreg, hk, hnot⟩ | h)
    · left
      exact ⟨i, ⟨hi, (not_isBoundAt_iff hi).1 hreg⟩, hk, hnot⟩
    · right; exact h

/-! ### The arguments against the binders -/

theorem argsOk_length {st : State} : ∀ {bs : List Binder} {ps : List ℕ}, argsOk st bs ps → ps.length = bs.length
  | [], [], _ => rfl
  | _ :: bs, _ :: ps, h => by simp [argsOk_length h.2]
  | [], _ :: _, h => by simp [argsOk] at h
  | _ :: _, [], h => by simp [argsOk] at h

theorem argsOk_get {st : State} : ∀ {bs : List Binder} {ps : List ℕ}, argsOk st bs ps →
    ∀ (i : ℕ) (b : Binder) (p : ℕ), bs[i]? = some b → ps[i]? = some p →
      ∃ ty, st.ty p = some ty ∧ ty.sort = b.sort ∧ (b.bound → ty.bound)
  | [], [], _, i, _, _, hb, _ => by simp at hb
  | b' :: bs, p' :: ps, h, i, b, p, hb, hp => by
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hb hp
      subst hb; subst hp
      exact h.1
    | succ i =>
      simp only [List.getElem?_cons_succ] at hb hp
      exact argsOk_get h.2 i b p hb hp
  | [], _ :: _, h, _, _, _, _, _ => by simp [argsOk] at h
  | _ :: _, [], h, _, _, _, _, _ => by simp [argsOk] at h

/-- A node of the store, with its type. -/
theorem State.ty_eq {st : State} {p : ℕ} {n : Node} (h : st.store[p]? = some n) : st.ty p = some n.ty := by
  simp [State.ty, h]

theorem State.ty_some {st : State} {p : ℕ} {ty : Ty} (h : st.ty p = some ty) : ∃ n, st.store[p]? = some n ∧ n.ty = ty := by
  simp only [State.ty, Option.map_eq_some_iff] at h
  exact h

/-- Arguments that the machine accepts fit the binders in the semantics; `all` is the
binder list the map is over (the term's own), which the induction leaves fixed. -/
theorem argsOk_forall₂_aux {E : env} {bs : List Binder} {ds : List ℕ} {isDef : Bool} {st : State}
    (hst : StoreOk E bs ds isDef st.store) (all : List Binder) :
    ∀ {tbs : List Binder} {ps : List ℕ}, argsOk st tbs ps →
      List.Forall₂ (sexpr.ok_bi E (ctxOf bs ds)) (ps.map (toSexpr st.store)) (tbs.map (Binder.toMm0 all))
  | [], [], _ => List.Forall₂.nil
  | [], _ :: _, h => by simp [argsOk] at h
  | _ :: _, [], h => by simp [argsOk] at h
  | b :: tbs, p :: ps, h => by
    obtain ⟨⟨ty, hty, hsort, hbound⟩, hrest⟩ := h
    simp only [List.map_cons]
    refine List.Forall₂.cons ?_ (argsOk_forall₂_aux hst all hrest)
    obtain ⟨n, hn, rfl⟩ := State.ty_some hty
    have hok := hst.nodes p n hn
    cases hbb : b.bound with
    | true =>
      rw [toMm0_bound hbb]
      simp only [sexpr.ok_bi]
      obtain ⟨v, s, hnv, hv⟩ := hok.bound.1 (hbound hbb)
      rw [hnv] at hn
      refine ⟨v, toSexpr_var hn, ?_⟩
      have hokv := hok.ok
      rw [toSexpr_var hn] at hokv
      obtain ⟨bi, hv', _, hs⟩ := ok'_var_inv hokv
      rw [hv] at hv'
      simp only [Option.some.injEq] at hv'
      subst hv'
      simp only [binder.sort] at hs
      rw [hv, ← hsort, hs]
    | false =>
      rw [toMm0_reg hbb]
      simp only [sexpr.ok_bi]
      rw [← hsort]
      exact hok.ok

theorem argsOk_forall₂ {E : env} {bs : List Binder} {ds : List ℕ} {isDef : Bool} {st : State}
    (hst : StoreOk E bs ds isDef st.store) {tbs : List Binder} {ps : List ℕ} (h : argsOk st tbs ps) :
    List.Forall₂ (sexpr.ok_bi E (ctxOf bs ds)) (ps.map (toSexpr st.store)) (tbs.map (Binder.toMm0 tbs)) :=
  argsOk_forall₂_aux hst tbs h

end Verifier
