/-
The binders loaded (milestone V3, part b): the invariant along `LoadArgs`, the loaded
store's meaning, and the context well-formed (`ctx.ok`).
-/
import Verifier.StepStore

namespace Verifier

open mm0

/-- The state while the first `i` binders are loaded. -/
structure Loading (c : Ctx) (bs : List Binder) (i : ℕ) (st : State) : Prop where
  le : i ≤ bs.length
  len : st.store.length = i
  nodes : ∀ j, j < i → ∃ b, bs[j]? = some b ∧ st.store[j]? = some (Node.var (Ty.ofBinder b) j)
  nextBv : st.nextBv = countBefore bs i
  nextVar : st.nextVar = i
  heap : st.heap = (List.range i).map El.expr
  stack : st.stack = []
  hyps : st.hyps = []
  wf : ∀ j b, j < i → bs[j]? = some b →
    (b.bound = true → b.deps = {countBefore bs j} ∧ ∃ sd, c.sorts[b.sort]? = some sd ∧ sd.strict = false) ∧
    (b.bound = false → b.sort < c.sorts.length ∧ ∀ k ∈ b.deps, k < countBefore bs j)

theorem loading_empty (c : Ctx) (bs : List Binder) : Loading c bs 0 State.empty :=
  ⟨Nat.zero_le _, rfl, fun _ h => absurd h (Nat.not_lt_zero _), rfl, rfl, rfl, rfl, rfl,
   fun _ _ h => absurd h (Nat.not_lt_zero _)⟩

theorem loadArgs_loading {c : Ctx} {bs : List Binder} : ∀ {bs' : List Binder} {st st' : State} {i : ℕ},
    LoadArgs c bs' st st' → bs' = bs.drop i → Loading c bs i st → Loading c bs bs.length st'
  | _, st, _, i, LoadArgs.nil _, hdrop, h => by
    have : i = bs.length := by
      have hl := congrArg List.length hdrop
      rw [List.length_drop] at hl
      simp only [List.length_nil] at hl
      have := h.le
      omega
    subst this
    exact h
  | _, st, st', i, LoadArgs.bound b bs' _ _ sd hbb hsd hstrict _ hdeps hrest, hdrop, h => by
    have hlt : i < bs.length := by
      by_contra hge
      rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hge)] at hdrop
      cases hdrop
    rw [List.drop_eq_getElem_cons hlt] at hdrop
    simp only [List.cons.injEq] at hdrop
    obtain ⟨rfl, hdrop⟩ := hdrop
    have hb : bs[i]? = some bs[i] := List.getElem?_eq_getElem hlt
    have hbound : isBoundAt bs i := isBoundAt_iff.2 ⟨_, hb, hbb⟩
    refine loadArgs_loading hrest hdrop ⟨by omega, ?_, ?_, ?_, ?_, ?_, h.stack, h.hyps, ?_⟩
    · simp [h.len]
    · intro j hj
      by_cases hji : j < i
      · obtain ⟨b', hb', hn⟩ := h.nodes j hji
        exact ⟨b', hb', by rw [List.getElem?_append_left (by rw [h.len]; exact hji)]; exact hn⟩
      · have : j = i := by omega
        subst this
        refine ⟨bs[j], hb, ?_⟩
        show (st.store ++ [Node.var (Ty.ofBinder bs[j]) st.nextVar])[j]? = some (Node.var (Ty.ofBinder bs[j]) j)
        rw [List.getElem?_append_right (by have := h.len; omega), h.len, Nat.sub_self]
        simp only [List.getElem?_cons_zero, Option.some.injEq]
        rw [h.nextVar]
    · show st.nextBv + 1 = countBefore bs (i + 1)
      rw [h.nextBv, countBefore_succ_of_bound hbound]
    · show st.nextVar + 1 = i + 1
      rw [h.nextVar]
    · show st.heap ++ [El.expr st.store.length] = _
      rw [h.heap, h.len, List.range_succ, List.map_append]
      rfl
    · intro j b' hj hb'
      by_cases hji : j < i
      · exact h.wf j b' hji hb'
      · have : j = i := by omega
        subst this
        rw [hb] at hb'
        simp only [Option.some.injEq] at hb'
        subst hb'
        refine ⟨fun _ => ⟨?_, sd, hsd, hstrict⟩, fun hf => Bool.noConfusion (hbb.symm.trans hf)⟩
        rw [hdeps, h.nextBv]
  | _, st, st', i, LoadArgs.reg b bs' _ _ hbb hsort hdeps hrest, hdrop, h => by
    have hlt : i < bs.length := by
      by_contra hge
      rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hge)] at hdrop
      cases hdrop
    rw [List.drop_eq_getElem_cons hlt] at hdrop
    simp only [List.cons.injEq] at hdrop
    obtain ⟨rfl, hdrop⟩ := hdrop
    have hb : bs[i]? = some bs[i] := List.getElem?_eq_getElem hlt
    have hreg : ¬ isBoundAt bs i := by
      rw [not_isBoundAt_iff hlt, List.getElem?_eq_getElem hlt]
      simp [hbb]
    refine loadArgs_loading hrest hdrop ⟨by omega, ?_, ?_, ?_, ?_, ?_, h.stack, h.hyps, ?_⟩
    · simp [h.len]
    · intro j hj
      by_cases hji : j < i
      · obtain ⟨b', hb', hn⟩ := h.nodes j hji
        exact ⟨b', hb', by rw [List.getElem?_append_left (by rw [h.len]; exact hji)]; exact hn⟩
      · have : j = i := by omega
        subst this
        refine ⟨bs[j], hb, ?_⟩
        show (st.store ++ [Node.var (Ty.ofBinder bs[j]) st.nextVar])[j]? = some (Node.var (Ty.ofBinder bs[j]) j)
        rw [List.getElem?_append_right (by have := h.len; omega), h.len, Nat.sub_self]
        simp only [List.getElem?_cons_zero, Option.some.injEq]
        rw [h.nextVar]
    · show st.nextBv = countBefore bs (i + 1)
      rw [h.nextBv, countBefore_succ_of_reg hreg]
    · show st.nextVar + 1 = i + 1
      rw [h.nextVar]
    · show st.heap ++ [El.expr st.store.length] = _
      rw [h.heap, h.len, List.range_succ, List.map_append]
      rfl
    · intro j b' hj hb'
      by_cases hji : j < i
      · exact h.wf j b' hji hb'
      · have : j = i := by omega
        subst this
        rw [hb] at hb'
        simp only [Option.some.injEq] at hb'
        subst hb'
        refine ⟨fun hf => Bool.noConfusion (hbb.symm.trans hf), fun _ => ⟨hsort, ?_⟩⟩
        intro k hk
        have := hdeps k hk
        rw [h.nextBv] at this
        exact this

/-- The binders loaded: well-formed, and the store means them. -/
theorem loaded_bindersWF {c : Ctx} {bs : List Binder} {st : State} (h : Loading c bs bs.length st) : BindersWF bs := by
  intro i b hb
  have hi := (List.getElem?_eq_some_iff.1 hb).1
  obtain ⟨h1, h2⟩ := h.wf i b hi hb
  exact ⟨fun hbb => (h1 hbb).1, fun hbb => (h2 hbb).2⟩

theorem loaded_storeOk {E : env} {c : Ctx} {bs : List Binder} {isDef : Bool} {st : State}
    (h : Loading c bs bs.length st) : StoreOk E bs [] isDef st.store := by
  have hwf := loaded_bindersWF h
  refine ⟨?_, ?_⟩
  · intro p ty t args hp
    by_cases hpl : p < bs.length
    · obtain ⟨b, _, hn⟩ := h.nodes p hpl
      rw [hn] at hp
      cases hp
    · rw [List.getElem?_eq_none_iff.2 (by rw [h.len]; omega)] at hp
      cases hp
  · intro p n hp
    have hpl : p < bs.length := by
      have := (List.getElem?_eq_some_iff.1 hp).1
      rwa [h.len] at this
    obtain ⟨b, hb, hn⟩ := h.nodes p hpl
    rw [hn] at hp
    simp only [Option.some.injEq] at hp
    subst hp
    exact nodeOk_binder hwf hb hn

theorem loaded_stateOk {E : env} {c : Ctx} {bs : List Binder} {isDef : Bool} {st : State}
    (h : Loading c bs bs.length st) : StateOk E bs [] isDef st :=
  ⟨loaded_storeOk h, by rw [h.nextBv, countBefore_length]; rfl, by rw [h.nextVar]; rfl⟩

end Verifier
