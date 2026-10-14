/-
Facts about runs (milestone V3, part d): what a step extends, the dummies a run makes,
the terms in the store, and the machine's checks carried to a longer store.
-/
import Verifier.UnifyUse
import Verifier.Sexpr2

namespace Verifier

open mm0
open Whitehead.Mmb (ProofCmd)

/-! ### A longer store -/

theorem toSexprF_prefix {store : List Node} (hwf : StoreWF store) (tl : List Node) :
    ∀ (fuel p : ℕ), p < store.length → toSexprF (store ++ tl) fuel p = toSexprF store fuel p
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
        exact toSexprF_prefix hwf tl fuel q (lt_trans (hwf p ty t args hq q hq') hp)

theorem toSexpr_prefix {store store' : List Node} (hwf : StoreWF store) (h : store <+: store') {p : ℕ}
    (hp : p < store.length) : toSexpr store' p = toSexpr store p := by
  obtain ⟨tl, rfl⟩ := h
  exact toSexprF_prefix hwf tl (p + 1) p hp

theorem getElem?_prefix {α : Type} {l l' : List α} (h : l <+: l') {i : ℕ} {a : α} (hi : l[i]? = some a) :
    l'[i]? = some a := by
  obtain ⟨tl, rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hi).1]
  exact hi

/-- The state with a longer store. -/
def State.withStore (st : State) (store : List Node) : State := { st with store }

theorem ty_prefix {st : State} {store : List Node} (h : st.store <+: store) {p : ℕ} {ty : Ty}
    (hp : st.ty p = some ty) : (st.withStore store).ty p = some ty := by
  obtain ⟨n, hn, rfl⟩ := State.ty_some hp
  simp [State.ty, State.withStore, getElem?_prefix h hn]

theorem argsOk_prefix {st : State} {store : List Node} (h : st.store <+: store) :
    ∀ {bs : List Binder} {ps : List ℕ}, argsOk st bs ps → argsOk (st.withStore store) bs ps
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨⟨ty, hty, hs, hb⟩, hr⟩ => ⟨⟨ty, ty_prefix h hty, hs, hb⟩, argsOk_prefix h hr⟩
  | [], _ :: _, hr => by simp [argsOk] at hr
  | _ :: _, [], hr => by simp [argsOk] at hr

theorem thmDisjoint_prefix {st : State} {store : List Node} (h : st.store <+: store) :
    ∀ {bs : List Binder} {ps : List ℕ} {seen : List (ℕ × Finset ℕ)} {earlier : List (Finset ℕ)},
      thmDisjoint st bs ps seen earlier → thmDisjoint (st.withStore store) bs ps seen earlier
  | [], [], _, _, _ => trivial
  | b :: bs, p :: ps, seen, earlier, ⟨ty, hty, hrest⟩ => by
    refine ⟨ty, ty_prefix h hty, ?_⟩
    cases hb : b.bound
    · simp only [hb, Bool.false_eq_true, ite_false] at hrest ⊢
      exact ⟨hrest.1, thmDisjoint_prefix h hrest.2⟩
    · simp only [hb, ite_true] at hrest ⊢
      exact ⟨hrest.1, thmDisjoint_prefix h hrest.2⟩
  | [], _ :: _, _, _, hr => by simp [thmDisjoint] at hr
  | _ :: _, [], _, _, hr => by simp [thmDisjoint] at hr

/-! ### Popping arguments -/

theorem popArgs_spec : ∀ {n : ℕ} {S : List El} {args : List ℕ} {S' : List El},
    popArgs n S args S' → args.length = n ∧ S = args.reverse.map El.expr ++ S'
  | _, _, _, _, popArgs.zero _ => ⟨rfl, rfl⟩
  | _, _, _, _, popArgs.succ _ _ p _ _ h => by
    obtain ⟨hl, hS⟩ := popArgs_spec h
    refine ⟨by simp [hl], ?_⟩
    simp [hS]

/-! ### What a step extends -/

/-- The store, the heap and the hypotheses only grow. -/
structure Ext (st st' : State) : Prop where
  store : st.store <+: st'.store
  heap : st.heap <+: st'.heap
  hyps : st.hyps <+: st'.hyps

theorem Ext.refl (st : State) : Ext st st := ⟨List.prefix_rfl, List.prefix_rfl, List.prefix_rfl⟩

theorem Ext.trans {a b c : State} (h₁ : Ext a b) (h₂ : Ext b c) : Ext a c :=
  ⟨h₁.store.trans h₂.store, h₁.heap.trans h₂.heap, h₁.hyps.trans h₂.hyps⟩


theorem step_ext {c : Ctx} {cmd : ProofCmd} {st st' : State} (h : Step c cmd st st') : Ext st st' := by
  cases h
  case term => exact ⟨List.prefix_append _ _, prefix_ite _ _ _, List.prefix_rfl⟩
  case dummy => exact ⟨List.prefix_append _ _, List.prefix_append _ _, List.prefix_rfl⟩
  case thm => exact ⟨List.prefix_rfl, prefix_ite _ _ _, List.prefix_rfl⟩
  case hyp => exact ⟨List.prefix_rfl, List.prefix_append _ _, List.prefix_append _ _⟩
  case convSave => exact ⟨List.prefix_rfl, List.prefix_append _ _, List.prefix_rfl⟩
  case save => exact ⟨List.prefix_rfl, List.prefix_append _ _, List.prefix_rfl⟩
  all_goals exact ⟨List.prefix_rfl, List.prefix_rfl, List.prefix_rfl⟩

theorem run_ext {c : Ctx} : ∀ {cmds : List ProofCmd} {st st' : State}, Run c cmds st st' → Ext st st'
  | _, _, _, Run.nil _ => Ext.refl _
  | _, _, _, Run.cons _ _ _ _ _ hs hr => (step_ext hs).trans (run_ext hr)

/-! ### The dummies of a run -/

def dummyOf : ProofCmd → List ℕ
  | ProofCmd.dummy s => [s]
  | _ => []

def dummiesOf (cmds : List ProofCmd) : List ℕ := cmds.flatMap dummyOf

theorem stepCtx_eq {cmd : ProofCmd} {ds ds' : List ℕ} (h : StepCtx cmd ds ds') : ds' = ds ++ dummyOf cmd := by
  rcases h with ⟨rfl, hne⟩ | ⟨s, rfl, rfl⟩
  · cases cmd
    case dummy s => exact absurd rfl (hne s)
    all_goals simp [dummyOf]
  · rfl

theorem run_stateOk_exact {E : env} {c : Ctx} {allTerms : List TermDecl} (hE : EnvHas E c allTerms)
    {bs : List Binder} (hwf : BindersWF bs) : ∀ {cmds : List ProofCmd} {st st' : State} {ds : List ℕ},
      Run c cmds st st' → StateOk E bs ds c.isDef st → StateOk E bs (ds ++ dummiesOf cmds) c.isDef st'
  | _, _, _, ds, Run.nil _, h => by simpa [dummiesOf] using h
  | _, _, _, ds, Run.cons cmd _ _ _ _ hstep hrun, h => by
    obtain ⟨ds₁, hctx, h₁⟩ := step_stateOk hE hwf hstep h
    have := run_stateOk_exact hE hwf hrun h₁
    rw [stepCtx_eq hctx] at this
    simpa [dummiesOf, List.append_assoc] using this

/-- The dummies' sorts are declared and not strict. -/
def SortsOk (c : Ctx) (ds : List ℕ) : Prop := ∀ s ∈ ds, ∃ sd, c.sorts[s]? = some sd ∧ sd.strict = false

theorem run_sortsOk {c : Ctx} : ∀ {cmds : List ProofCmd} {st st' : State}, Run c cmds st st' → SortsOk c (dummiesOf cmds)
  | _, _, _, Run.nil _ => fun s h => by simp [dummiesOf] at h
  | _, _, _, Run.cons cmd _ _ _ _ hstep hrun => by
    intro s hs
    simp only [dummiesOf, List.flatMap_cons, List.mem_append] at hs
    rcases hs with hs | hs
    · cases hstep
      case dummy s' sd hsd hstrict _ _ =>
        simp only [dummyOf, List.mem_singleton] at hs
        subst hs
        exact ⟨sd, hsd, hstrict⟩
      all_goals simp [dummyOf] at hs
    · exact run_sortsOk hrun s hs

/-! ### The terms in the store -/

theorem storeTerms_step {c : Ctx} {cmd : ProofCmd} {st st' : State} (h : Step c cmd st st') :
    StoreTerms c st.store → StoreTerms c st'.store := by
  intro hT
  cases h
  case term t save decl args S' ty hdecl hpop _ _ =>
    intro p ty' t' args' hp
    by_cases hlt : p < st.store.length
    · rw [List.getElem?_append_left hlt] at hp
      exact hT p ty' t' args' hp
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hp
      cases hpl : p - st.store.length with
      | zero =>
        rw [hpl] at hp
        simp only [List.getElem?_cons_zero, Option.some.injEq, Node.app.injEq] at hp
        obtain ⟨_, rfl, rfl⟩ := hp
        exact ⟨decl, hdecl, (popArgs_spec hpop).1⟩
      | succ k => rw [hpl] at hp; simp at hp
  case dummy =>
    intro p ty' t' args' hp
    by_cases hlt : p < st.store.length
    · rw [List.getElem?_append_left hlt] at hp
      exact hT p ty' t' args' hp
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hp
      cases hpl : p - st.store.length with
      | zero => rw [hpl] at hp; simp at hp
      | succ k => rw [hpl] at hp; simp at hp
  all_goals exact hT

theorem storeTerms_run {c : Ctx} : ∀ {cmds : List ProofCmd} {st st' : State}, Run c cmds st st' →
    StoreTerms c st.store → StoreTerms c st'.store
  | _, _, _, Run.nil _, h => h
  | _, _, _, Run.cons _ _ _ _ _ hs hr, h => storeTerms_run hr (storeTerms_step hs h)

end Verifier
