/-
A statement the machine accepts (milestone V3, part g): a theorem proves its decoded
statement in its context with its dummies (`env.proof'.thm`), and a def's value is
well-typed over its binders and the dummies of its stream.
-/
import Verifier.RunSound

namespace Verifier

open mm0
open Whitehead.Mmb (ProofCmd UnifyCmd)

/-! ### After the binders are loaded -/

theorem loaded_storeTerms {c : Ctx} {bs : List Binder} {st : State} (h : Loading c bs bs.length st) :
    StoreTerms c st.store := by
  intro p ty t args hp
  have hpl : p < bs.length := by
    have := (List.getElem?_eq_some_iff.1 hp).1
    rwa [h.len] at this
  obtain ⟨b, _, hn⟩ := h.nodes p hpl
  rw [hn] at hp
  cases hp

theorem loaded_heapOk {W : World} {c : Ctx} {bs : List Binder} {st : State} (h : Loading c bs bs.length st) :
    HeapOk W st.store.length st.heap := by
  intro el hel
  rw [h.heap] at hel
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hel
  refine ⟨?_, fun a b h => by cases h⟩
  show i < st.store.length
  rw [h.len]
  exact List.mem_range.1 hi

theorem argsUheap_eq {c : Ctx} {bs : List Binder} {st st' : State} (h : Loading c bs bs.length st)
    (hext : st.heap <+: st'.heap) : argsUheap st' bs.length = argHeap (List.range bs.length) := by
  unfold argsUheap argHeap
  rw [← List.filterMap_eq_map]
  apply List.filterMap_congr
  intro i hi
  have hi' := List.mem_range.1 hi
  rw [getElem?_prefix hext (by rw [h.heap, List.getElem?_map, List.getElem?_range hi']; rfl)]
  rfl

theorem loaded_var {c : Ctx} {bs : List Binder} {st : State} (h : Loading c bs bs.length st) {store : List Node}
    (hpre : st.store <+: store) {i : ℕ} (hi : i < bs.length) : toSexpr store i = sexpr.var i := by
  obtain ⟨b, _, hn⟩ := h.nodes i hi
  exact toSexpr_var (getElem?_prefix hpre hn)

theorem range_map_toSexpr {c : Ctx} {bs : List Binder} {st : State} (h : Loading c bs bs.length st)
    {store : List Node} (hpre : st.store <+: store) :
    (List.range bs.length).map (toSexpr store) = (List.range bs.length).map sexpr.var :=
  List.map_congr_left fun _ hi => loaded_var h hpre (List.mem_range.1 hi)

/-! ### Dummies in the context -/

theorem ctxOk_dummies {E : env} {c : Ctx} {allTerms : List TermDecl} (hE : EnvHas E c allTerms) :
    ∀ (D : List ℕ) {Γ : ctx}, ctx.ok E Γ → SortsOk c D → ctx.ok E (Γ ++ D.map binder.bound)
  | [], Γ, h, _ => by simpa using h
  | s :: D, Γ, h, hs => by
    obtain ⟨sd, hsd, hstrict⟩ := hs s (List.mem_cons_self ..)
    have h' : ctx.ok E (Γ ++ [binder.bound s]) := ctx.ok.bound (hE.sorts _ _ hsd) (by simp [hstrict]) h
    have := ctxOk_dummies hE D h' (fun s' hs' => hs s' (List.mem_cons_of_mem _ hs'))
    simpa using this

/-! ### A theorem -/

theorem thm_stmt_sound {E : env} {c : Ctx} {allTerms : List TermDecl} (hE : EnvHas E c allTerms)
    (hdef : c.isDef = false) {decl : ThmDecl} {isAx : Bool} {body : List ProofCmd}
    (h : ThmOk c decl isAx body) :
    ∃ concl hl, decodeThm allTerms decl.args.length decl.unify = some (concl, hl) ∧
      (isAx = false → ∃ D, ctx.ok E (append_dummies (decl.args.map (Binder.toMm0 decl.args)) D) ∧
        proof E (append_dummies (decl.args.map (Binder.toMm0 decl.args)) D) {x | x ∈ hl} concl) := by
  have hc : { c with isDef := false } = c := by cases c; simp_all
  obtain ⟨st, st', e, ty, sd, hload, hrun, hstk, hty, hsd, hprov, hU⟩ := h
  rw [hc] at hrun hU
  have hL := loadArgs_loading hload (by simp) (loading_empty c decl.args)
  have hbwf := loaded_bindersWF hL
  have hst : StateOk E decl.args [] c.isDef st := loaded_stateOk hL
  have hT := loaded_storeTerms hL
  set D := dummiesOf body
  have hfin : StateOk E decl.args D c.isDef st' := by simpa using run_stateOk_exact hE hbwf hrun hst
  have hx := run_ext hrun
  have hT' := storeTerms_run hrun hT
  -- the statement, from the stream
  rw [argsUheap_eq hL hx.heap] at hU
  obtain ⟨concl, hl, hdec, hsx, hvl, hall⟩ := unify_end hfin.store.wf hT' hE.terms_prefix hU
  simp only [List.length_range] at hdec hvl hall
  refine ⟨concl, hl, hdec, fun hax => ⟨D, ?_, ?_⟩⟩
  · -- the context
    have h0 := ctxOk_loaded hE hL
    have := ctxOk_dummies hE D h0 (run_sortsOk hrun)
    simpa [ctxOf, append_dummies] using this
  · -- the proof, from the run
    subst hax
    set W : World := ⟨E, ctxOf decl.args D, st'.store, st'.hyps⟩
    have hW : WorldOk W c allTerms decl.args D := ⟨hE, rfl, hfin.store⟩
    have hS0 : SOk W st.store.length st.stack := by rw [hL.stack]; trivial
    obtain ⟨hS, _⟩ := run_sound hW hbwf hrun hst hT List.prefix_rfl List.prefix_rfl hS0 (loaded_heapOk hL)
    rw [hstk] at hS
    have hp : proof E (ctxOf decl.args D) W.Hs (W.x e) := hS.1.2
    have hxe : W.x e = concl := by
      show toSexpr st'.store e = concl
      rw [hsx, range_map_toSexpr hL hx.store, subst_id_of_varsLt hvl]
    have hHs : W.Hs = {x | x ∈ hl} := by
      ext x
      simp only [World.Hs, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h, hh, rfl⟩
        obtain ⟨y, hy, hhy⟩ := forall₂_mem_left hall h (List.mem_reverse.2 hh)
        rw [hhy.1, range_map_toSexpr hL hx.store, subst_id_of_varsLt hhy.2]
        exact hy
      · intro hx'
        obtain ⟨h, hh, hhy⟩ := forall₂_mem_right hall x hx'
        refine ⟨h, List.mem_reverse.1 hh, ?_⟩
        rw [hhy.1, range_map_toSexpr hL hx.store, subst_id_of_varsLt hhy.2]
    rw [hxe, hHs] at hp
    simpa [ctxOf, append_dummies] using hp

/-! ### A term or a def -/

/-- The dummies of a stream, as variables of the final context. -/
theorem dummy_vars {E : env} {bs : List Binder} {D : List ℕ} {isDef : Bool} {store : List Node}
    (hfin : StoreOk E bs D isDef store) {n : ℕ} {σ' : List sexpr} {ds : List ℕ}
    (hdum : DummiesCorr store n σ' ds) {j : ℕ} (hj : j < ds.length) :
    ∃ z, σ'[n + j]? = some (sexpr.var z) ∧ (ctxOf bs D)[z]? = some (binder.bound ds[j]) := by
  obtain ⟨v0, ty0, p0, hv0, hp0, hb0, hs0⟩ := hdum j ds[j] (List.getElem?_eq_getElem hj)
  refine ⟨v0, hv0, ?_⟩
  have hok := hfin.nodes p0 _ hp0
  obtain ⟨v1, s1, hv1, hΓ⟩ := hok.bound.1 hb0
  simp only [Node.var.injEq] at hv1
  obtain ⟨_, rfl⟩ := hv1
  have hok0 := hok.ok
  rw [toSexpr_var hp0] at hok0
  obtain ⟨bi, hbi, _, hbs⟩ := ok'_var_inv hok0
  rw [hΓ] at hbi
  simp only [Option.some.injEq] at hbi
  subst hbi
  simp only [binder.sort] at hbs
  rw [hΓ]
  have : s1 = ds[j] := by rw [← hbs]; exact hs0
  rw [this]

/-- What a term or def statement establishes about its declaration. -/
structure TermFacts (E : env) (c : Ctx) (allTerms : List TermDecl) (decl : TermDecl) : Prop where
  wf : BindersWF decl.args
  ret_deps : ∀ m ∈ decl.ret.deps, m < (boundNumbers decl.args).length
  ret_sort : ∃ sd, c.sorts[decl.ret.sort]? = some sd ∧ sd.pure = false
  ret_bound : decl.ret.bound = false
  value : ∀ us, decl.defn = some us → ∃ v ds, decodeDef allTerms decl.args.length us = some (v, ds) ∧
    sexpr.ok E (ctxOf decl.args ds) v decl.ret.sort

theorem term_stmt_sound {E : env} {c : Ctx} {allTerms : List TermDecl} (hE : EnvHas E c allTerms)
    {decl : TermDecl} (hdef : decl.defn.isSome → c.isDef = true) {isLocal : Bool} {body : List ProofCmd}
    (h : TermOk c decl isLocal body) : TermFacts E c allTerms decl := by
  obtain ⟨_, st, hload, hrb, hrs, hrd, hmatch⟩ := h
  have hL := loadArgs_loading hload (by simp) (loading_empty c decl.args)
  have hbwf := loaded_bindersWF hL
  refine ⟨hbwf, fun m hm => ?_, hrs, hrb, fun us hus => ?_⟩
  · have := hrd m hm
    rwa [hL.nextBv, countBefore_length] at this
  · have hc : { c with isDef := true } = c := by
      have := hdef (by rw [hus]; rfl)
      cases c; simp_all
    rw [hus] at hmatch
    obtain ⟨st', e, ty, hrun, hstk, hty, hsort, _, hU⟩ := hmatch
    rw [hc] at hrun hU
    have hst : StateOk E decl.args [] c.isDef st := loaded_stateOk hL
    have hT := loaded_storeTerms hL
    set D := dummiesOf body
    have hfin : StateOk E decl.args D c.isDef st' := by simpa using run_stateOk_exact hE hbwf hrun hst
    have hx := run_ext hrun
    have hT' := storeTerms_run hrun hT
    rw [argsUheap_eq hL hx.heap] at hU
    obtain ⟨v, ds, σ', hdec, hσpre, hσlen, hdum, hsx, hvl, -⟩ := unify_defn hfin.store.wf hT' hE.terms_prefix hU
    simp only [List.length_range] at hdec hσlen hdum
    refine ⟨v, ds, hdec, ?_⟩
    -- the value's node, well-typed at the result sort in the final context
    obtain ⟨n0, hn0, rfl⟩ := State.ty_some hty
    have hok := (hfin.store.nodes e n0 hn0).ok
    rw [hsort, hsx] at hok
    -- the substitution: the binders' variables, then the dummies' variables
    rw [range_map_toSexpr hL hx.store] at hσpre
    have hρ : ∀ i, i < (ctxOf decl.args ds).length → ∃ w, σ'.getD i default = sexpr.var w ∧
        (ctxOf decl.args D)[w]? = (ctxOf decl.args ds)[i]? := by
      intro i hi
      rw [ctxOf_length] at hi
      obtain ⟨tl, htl⟩ := hσpre
      by_cases hia : i < decl.args.length
      · refine ⟨i, ?_, ?_⟩
        · rw [← htl, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hia)]
          simp [hia]
        · rw [ctxOf_getElem_binder D (List.getElem?_eq_getElem hia), ctxOf_getElem_binder ds (List.getElem?_eq_getElem hia)]
      · have hj : i - decl.args.length < ds.length := by omega
        obtain ⟨z, hz, hΓ⟩ := dummy_vars hfin.store hdum hj
        rw [Nat.add_sub_cancel' (Nat.le_of_not_lt hia)] at hz
        refine ⟨z, by rw [List.getD_eq_getElem?_getD, hz]; rfl, ?_⟩
        rw [hΓ]
        have := ctxOf_getElem_dummy decl.args (List.getElem?_eq_getElem hj)
        rw [Nat.add_sub_cancel' (Nat.le_of_not_lt hia)] at this
        rw [this]
    exact ok'_of_subst_renaming hρ v (by rw [ctxOf_length, ← hσlen]; exact hvl) hok

end Verifier
