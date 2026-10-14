/-
The store through the commands (milestone V3, part b): every step keeps the meaning of
the nodes, a `Dummy` extending the context by its sort, `Term` adding an application.
-/
import Verifier.AppDef

namespace Verifier

open mm0
open Whitehead.Mmb (ProofCmd)

/-- The state's counters agree with the binders and the dummies, and the store means
what its type words say. -/
structure StateOk (E : env) (bs : List Binder) (ds : List ℕ) (isDef : Bool) (st : State) : Prop where
  store : StoreOk E bs ds isDef st.store
  nextBv : st.nextBv = nbv bs ds
  nextVar : st.nextVar = bs.length + ds.length

/-- A node keeps its meaning when the store grows. -/
theorem nodeOk_store_ext {E : env} {bs : List Binder} {ds : List ℕ} {isDef : Bool} {store : List Node}
    (hstore : StoreWF store) (m : Node) {p : ℕ} {n : Node} (hn : store[p]? = some n)
    (h : NodeOk E bs ds isDef store p n) : NodeOk E bs ds isDef (store ++ [m]) p n := by
  have hp : p < store.length := (List.getElem?_eq_some_iff.1 hn).1
  have hsx := toSexpr_append hstore m hp
  refine ⟨?_, h.bound, ?_⟩
  · rw [hsx]; exact h.ok
  · intro k
    rw [hsx]
    exact h.deps k

theorem storeOk_append_app {E : env} {bs : List Binder} {ds : List ℕ} {isDef : Bool} {store : List Node}
    (h : StoreOk E bs ds isDef store) {ty : Ty} {t : ℕ} {args : List ℕ} (hargs : ∀ q ∈ args, q < store.length)
    (hnew : NodeOk E bs ds isDef (store ++ [Node.app ty t args]) store.length (Node.app ty t args)) :
    StoreOk E bs ds isDef (store ++ [Node.app ty t args]) := by
  refine ⟨h.wf.append_app ty t hargs, ?_⟩
  intro p n hp
  by_cases hlt : p < store.length
  · rw [List.getElem?_append_left hlt] at hp
    exact nodeOk_store_ext h.wf _ hp (h.nodes p n hp)
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hp
    cases hpl : p - store.length with
    | zero =>
      rw [hpl] at hp
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
      subst hp
      have : p = store.length := by omega
      subst this
      exact hnew
    | succ k => rw [hpl] at hp; simp at hp

/-- A `Dummy` keeps the store's meaning, with the dummy's sort added to the context. -/
theorem storeOk_dummy {E : env} {bs : List Binder} (hwf : BindersWF bs) {ds : List ℕ} {isDef : Bool} {store : List Node}
    (h : StoreOk E bs ds isDef store) (s : ℕ) :
    StoreOk E bs (ds ++ [s]) isDef (store ++ [Node.var ⟨s, true, {nbv bs ds}⟩ (bs.length + ds.length)]) := by
  refine ⟨h.wf.append_var _ _, ?_⟩
  intro p n hp
  by_cases hlt : p < store.length
  · rw [List.getElem?_append_left hlt] at hp
    exact nodeOk_dummy_ext hwf h.wf s _ hp (h.nodes p n hp)
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hp
    cases hpl : p - store.length with
    | zero =>
      rw [hpl] at hp
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
      subst hp
      have : p = store.length := by omega
      subst this
      exact nodeOk_dummy s
    | succ k => rw [hpl] at hp; simp at hp

/-- What a step does to the context: nothing, or a dummy. -/
def StepCtx (cmd : ProofCmd) (ds ds' : List ℕ) : Prop :=
  (ds' = ds ∧ ∀ s, cmd ≠ ProofCmd.dummy s) ∨ ∃ s, cmd = ProofCmd.dummy s ∧ ds' = ds ++ [s]

/-- Every step keeps the state's meaning. -/
theorem step_stateOk {E : env} {c : Ctx} {allTerms : List TermDecl} (hE : EnvHas E c allTerms)
    {bs : List Binder} (hwf : BindersWF bs) {ds : List ℕ} {cmd : ProofCmd} {st st' : State}
    (hstep : Step c cmd st st') (h : StateOk E bs ds c.isDef st) :
    ∃ ds', StepCtx cmd ds ds' ∧ StateOk E bs ds' c.isDef st' := by
  cases hstep
  case term t save decl args S' ty hdecl hpop hargs hty =>
    refine ⟨ds, Or.inl ⟨rfl, fun _ h => by cases h⟩, ?_, h.nextBv, h.nextVar⟩
    subst hty
    have hvalid : ∀ p ∈ args, p < st.store.length := by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
      have hlen := argsOk_length hargs
      obtain ⟨ty', hty', _, _⟩ := argsOk_get hargs i decl.args[i] args[i]
        (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem hi)
      obtain ⟨n, hn, _⟩ := State.ty_some hty'
      exact (List.getElem?_eq_some_iff.1 hn).1
    apply storeOk_append_app h.store hvalid
    cases hdef : c.isDef with
    | true =>
      rw [hdef] at h
      exact nodeOk_app_def h.store hE hdecl hargs
    | false =>
      rw [hdef] at h
      exact nodeOk_app_thm h.store hE hdecl hargs
  case dummy s sd _ _ _ _ =>
    refine ⟨ds ++ [s], Or.inr ⟨s, rfl, rfl⟩, ?_, ?_, ?_⟩
    · have := storeOk_dummy hwf h.store s
      rw [h.nextBv, h.nextVar]
      exact this
    · show st.nextBv + 1 = nbv bs (ds ++ [s])
      rw [h.nextBv]
      unfold nbv
      rw [List.length_append, List.length_singleton]
      omega
    · show st.nextVar + 1 = bs.length + (ds ++ [s]).length
      rw [h.nextVar, List.length_append, List.length_singleton]
      omega
  all_goals exact ⟨ds, Or.inl ⟨rfl, fun _ h => by cases h⟩, h.store, h.nextBv, h.nextVar⟩

/-- A run keeps the state's meaning; the context grows by the dummies made. -/
theorem run_stateOk {E : env} {c : Ctx} {allTerms : List TermDecl} (hE : EnvHas E c allTerms)
    {bs : List Binder} (hwf : BindersWF bs) : ∀ {cmds : List ProofCmd} {st st' : State} {ds : List ℕ},
      Run c cmds st st' → StateOk E bs ds c.isDef st → ∃ ds', ds <+: ds' ∧ StateOk E bs ds' c.isDef st'
  | _, _, _, ds, Run.nil _, h => ⟨ds, List.prefix_rfl, h⟩
  | _, _, _, ds, Run.cons _ _ _ _ _ hstep hrun, h => by
    obtain ⟨ds₁, hctx, h₁⟩ := step_stateOk hE hwf hstep h
    obtain ⟨ds₂, hpre, h₂⟩ := run_stateOk hE hwf hrun h₁
    refine ⟨ds₂, ?_, h₂⟩
    rcases hctx with ⟨rfl, _⟩ | ⟨s, _, rfl⟩
    · exact hpre
    · exact (List.prefix_append ds [s]).trans hpre

end Verifier
