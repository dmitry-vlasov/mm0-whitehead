/-
Well-formedness of the declarations (milestone V3b): `term_ok`, `defn_ok` and
`axiom_ok` of `mm0.lean` for the declarations of a file the machine accepts.
-/
import Verifier.Free

namespace Verifier

open mm0
open Whitehead.Mmb (ProofCmd UnifyCmd)

/-! ### Contexts -/

theorem regDepsBound_ctxOf {bs : List Binder} (hwf : BindersWF bs) (ds : List ℕ) : RegDepsBound (ctxOf bs ds) := by
  intro u s vs hu x hx
  have hul : u < bs.length := by
    by_contra h
    have hd : u - bs.length < ds.length := by
      have := (List.getElem?_eq_some_iff.1 hu).1
      rw [ctxOf_length] at this
      omega
    have := ctxOf_getElem_dummy bs (List.getElem?_eq_getElem hd)
    rw [Nat.add_sub_cancel' (Nat.le_of_not_lt h), hu] at this
    cases this
  rw [ctxOf_getElem_binder ds (List.getElem?_eq_getElem hul)] at hu
  cases hb : bs[u].bound with
  | true => rw [toMm0_bound hb] at hu; cases hu
  | false =>
    rw [toMm0_reg hb] at hu
    simp only [Option.some.injEq, binder.reg.injEq] at hu
    obtain ⟨_, rfl⟩ := hu
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
    have hkl := lt_of_lt_of_le ((hwf u _ (List.getElem?_eq_getElem hul)).2 hb k hk) (countBefore_le_nb bs (le_of_lt hul))
    obtain ⟨b', hb', hbb'⟩ := isBoundAt_iff.1 (boundNumbers_bound hkl)
    refine ⟨b'.sort, ?_⟩
    rw [bvVar_of_lt hkl, ctxOf_getElem_binder ds hb', toMm0_bound hbb']

theorem termsRetBound_of {E : env} {c : Ctx} {allTerms : List TermDecl} (hE : EnvHas E c allTerms) : TermsRetBound E := by
  intro t a r o hg u hu
  obtain ⟨d, hd, rfl, rfl⟩ := hE.terms_unique t a r o hg
  obtain ⟨_, hret⟩ := hE.terms_wf t d hd
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hu
  have hml := hret m hm
  obtain ⟨b', hb', hbb'⟩ := isBoundAt_iff.1 (boundNumbers_bound hml)
  refine ⟨b'.sort, ?_⟩
  rw [bvVar_of_lt hml, List.getElem?_map, hb']
  simp [toMm0_bound hbb']

theorem ctx_ok_bound_lookup {E : env} : ∀ {Γ : ctx}, ctx.ok E Γ → ∀ {z : ℕ} {s : sort_id},
    Γ[z]? = some (binder.bound s) → ∃ sd, E.get_sd s sd ∧ ¬ sd.strict := by
  intro Γ h
  induction h with
  | nil => intro z s hz; simp at hz
  | @bound s' sd' Γ' hsd hstrict _ ih =>
    intro z s hz
    by_cases hzl : z < Γ'.length
    · rw [List.getElem?_append_left hzl] at hz
      exact ih hz
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hzl)] at hz
      cases hz' : z - Γ'.length with
      | zero =>
        rw [hz'] at hz
        simp only [List.getElem?_cons_zero, Option.some.injEq, binder.bound.injEq] at hz
        subst hz
        exact ⟨sd', hsd, hstrict⟩
      | succ k => rw [hz'] at hz; simp at hz
  | @reg s' vs Γ' _ _ ih =>
    intro z s hz
    by_cases hzl : z < Γ'.length
    · rw [List.getElem?_append_left hzl] at hz
      exact ih hz
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hzl)] at hz
      cases hz' : z - Γ'.length with
      | zero => rw [hz'] at hz; simp at hz
      | succ k => rw [hz'] at hz; simp at hz

theorem ctx_ok_append_bound {E : env} : ∀ (ds : List sort_id) {Γ : ctx}, ctx.ok E Γ →
    (∀ s ∈ ds, ∃ sd, E.get_sd s sd ∧ ¬ sd.strict) → ctx.ok E (Γ ++ ds.map binder.bound)
  | [], Γ, h, _ => by simpa using h
  | s :: ds, Γ, h, hs => by
    obtain ⟨sd, hsd, hstrict⟩ := hs s (List.mem_cons_self ..)
    have := ctx_ok_append_bound ds (ctx.ok.bound hsd hstrict h) (fun s' hs' => hs s' (List.mem_cons_of_mem _ hs'))
    simpa using this

theorem ok'_shrink {E : env} {Γ Δ : ctx} : ∀ {e : sexpr} {bis : List binder} {s : sort_id},
    sexpr.VarsLt e Γ.length → sexpr.ok' E (Γ ++ Δ) e bis s → sexpr.ok' E Γ e bis s
  | .var u, bis, s, hu, h => by
    obtain ⟨bi, hbi, rfl, rfl⟩ := ok'_var_inv h
    rw [List.getElem?_append_left hu] at hbi
    exact sexpr.ok'.var hbi
  | .term f, bis, s, _, h => by
    obtain ⟨ret, o, hg, rfl⟩ := ok'_term_inv h
    exact sexpr.ok'.term hg
  | .app1 f x, bis, s, hv, h => by
    obtain ⟨bi, hf, hx⟩ := ok'_app1_inv h
    have ihf := ok'_shrink hv.1 hf
    cases bi with
    | bound s0 =>
      obtain ⟨w, rfl, hw⟩ := hx
      have hwl : w < Γ.length := hv.2
      rw [List.getElem?_append_left hwl] at hw
      exact sexpr.ok'.app_var hw ihf
    | reg s0 vs => exact sexpr.ok'.app_reg ihf (ok'_shrink hv.2 hx)

/-! ### The dependency of a bound variable's node -/

theorem var_node_dep {E : env} {bs : List Binder} {D : List ℕ} {isDef : Bool} {store : List Node}
    (hst : StoreOk E bs D isDef store) {p : ℕ} {ty : Ty} {z : ℕ} (hp : store[p]? = some (Node.var ty z))
    {s : sort_id} (hz : (ctxOf bs D)[z]? = some (binder.bound s)) :
    ∃ k, bvVar bs k = z ∧ k ∈ ty.deps := by
  obtain ⟨k, hk, hkz⟩ := bvVar_of_bound hz
  refine ⟨k, hkz, ?_⟩
  have := ((hst.nodes p _ hp).deps k).2
  refine this ⟨hk, ?_⟩
  rw [toSexpr_var hp]
  unfold Dep
  cases isDef
  · simp only [Bool.false_eq_true, ite_false]
    rw [has_var_var_bound hz, hkz]
  · simp only [ite_true, sexpr.free, sexpr.free']
    rw [has_var_var_bound hz, hkz]

/-! ### A term or def statement -/

theorem term_stmt_wf {E : env} {c : Ctx} {allTerms : List TermDecl} (hE : EnvHas E c allTerms)
    {decl : TermDecl} (hdef : decl.defn.isSome → c.isDef = true) {isLocal : Bool} {body : List ProofCmd}
    (h : TermOk c decl isLocal body) :
    ctx.ok E (ctxOf decl.args []) ∧ dep_type.ok E (ctxOf decl.args []) (depTypeOf decl.args decl.ret) ∧
    ∀ us, decl.defn = some us → ∀ v ds, decodeDef allTerms decl.args.length us = some (v, ds) →
      ctx.ok E (ctxOf decl.args ds) ∧
      ∀ x, sexpr.free E (ctxOf decl.args ds) v x → x ∈ (depTypeOf decl.args decl.ret).2 := by
  have hfacts := term_stmt_sound hE hdef h
  have hu := hE.termsUnique
  have hr := termsRetBound_of hE
  obtain ⟨_, st, hload, hrb, hrs, hrd, hmatch⟩ := h
  have hL := loadArgs_loading hload (by simp) (loading_empty c decl.args)
  have hbwf := loaded_bindersWF hL
  have hctx0 := ctxOk_loaded hE hL
  obtain ⟨sd, hsd, _⟩ := hrs
  have hnb : ∀ m ∈ decl.ret.deps, m < (boundNumbers decl.args).length := hfacts.ret_deps
  refine ⟨hctx0, depTypeOk_of hE hsd hnb, fun us hus v ds hdec => ?_⟩
  have hc : { c with isDef := true } = c := by
    have := hdef (by rw [hus]; rfl)
    cases c; simp_all
  rw [hus] at hmatch
  obtain ⟨st', e, ty, hrun, hstk, hty, hsort, hdeps, hU⟩ := hmatch
  rw [hc] at hrun hU
  have hcdef : c.isDef = true := hdef (by rw [hus]; rfl)
  have hst : StateOk E decl.args [] c.isDef st := loaded_stateOk hL
  have hT := loaded_storeTerms hL
  set D := dummiesOf body
  have hfin : StateOk E decl.args D c.isDef st' := by simpa using run_stateOk_exact hE hbwf hrun hst
  rw [hcdef] at hfin
  have hx := run_ext hrun
  have hT' := storeTerms_run hrun hT
  rw [argsUheap_eq hL hx.heap] at hU
  obtain ⟨v', ds', σ', hdec', hσpre, hσlen, hdum, hsx, hvl, H', hdn⟩ := unify_defn hfin.store.wf hT' hE.terms_prefix hU
  simp only [List.length_range] at hdec' hσlen hdum hdn
  rw [hdec] at hdec'
  simp only [Option.some.injEq, Prod.mk.injEq] at hdec'
  obtain ⟨rfl, rfl⟩ := hdec'
  -- the contexts
  set n := decl.args.length with hn
  set Γ := ctxOf decl.args D with hΓ
  set Δ := ctxOf decl.args ds with hΔ
  have hΓok : ctx.ok E Γ := by
    have := ctxOk_dummies hE D hctx0 (run_sortsOk hrun)
    simpa [hΓ, ctxOf] using this
  have hdv : ∀ j (hj : j < ds.length), ∃ z, σ'[n + j]? = some (sexpr.var z) ∧ Γ[z]? = some (binder.bound ds[j]) :=
    fun j hj => dummy_vars hfin.store hdum hj
  refine ⟨?_, fun x hxf => ?_⟩
  · have := ctx_ok_append_bound ds hctx0 (fun s hs => ?_)
    · simpa [hΔ, ctxOf] using this
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
      obtain ⟨z, _, hz⟩ := hdv j hj
      exact ctx_ok_bound_lookup hΓok hz
  -- the value is well-typed over its context
  obtain ⟨v₀, ds₀, hdec₀, hvok⟩ := hfacts.value us hus
  rw [hdec] at hdec₀
  simp only [Option.some.injEq, Prod.mk.injEq] at hdec₀
  obtain ⟨rfl, rfl⟩ := hdec₀
  -- the substitution: the binders' variables, then the dummies' variables
  rw [range_map_toSexpr hL hx.store] at hσpre
  obtain ⟨tl, htl⟩ := hσpre
  have hΔlen : Δ.length = n + ds.length := by rw [hΔ, ctxOf_length]
  have hσ'len : σ'.length = Δ.length := by rw [hσlen, hΔlen]
  set r : ℕ → ℕ := fun i => getVar (σ'.getD i default) with hrdef
  have hrlow : ∀ i, i < n → σ'.getD i default = sexpr.var i := by
    intro i hi
    have hi' : i < decl.args.length := hi
    rw [← htl, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hi), List.getElem?_map,
      List.getElem?_range hi']
    rfl
  have hrlow' : ∀ i, i < n → r i = i := fun i hi => by
    show getVar (σ'.getD i default) = i
    rw [hrlow i hi]
    rfl
  have hrhigh : ∀ j (hj : j < ds.length), ∃ z, σ'.getD (n + j) default = sexpr.var z ∧ r (n + j) = z ∧
      Γ[z]? = some (binder.bound ds[j]) := by
    intro j hj
    obtain ⟨z, hz, hΓz⟩ := hdv j hj
    have hz' : σ'.getD (n + j) default = sexpr.var z := by rw [List.getD_eq_getElem?_getD, hz]; rfl
    refine ⟨z, hz', ?_, hΓz⟩
    show getVar (σ'.getD (n + j) default) = z
    rw [hz']
    rfl
  -- a dummy's variable and its dependency
  obtain ⟨_, dn, hdnl, hdn1, hdn2, _⟩ := hdn
  have hdummy_dep : ∀ j (hj : j < ds.length), ∃ k, bvVar decl.args k = r (n + j) ∧
      k ∈ depsAt st' (dn[j]'(by omega)) := by
    intro j hj
    obtain ⟨v0, ty0, hv0, hn0, _, _⟩ := hdn1 j (by omega)
    obtain ⟨z, hz, hrz, hΓz⟩ := hrhigh j hj
    rw [List.getD_eq_getElem?_getD, hv0] at hz
    simp only [Option.getD_some, sexpr.var.injEq] at hz
    subst hz
    obtain ⟨k, hk, hkd⟩ := var_node_dep hfin.store hn0 hΓz
    refine ⟨k, by rw [hrz, hk], ?_⟩
    simp [depsAt, State.ty, hn0, Node.ty, hkd]
  have hbinder_dep : ∀ i (hi : i < n), (∃ s, Γ[i]? = some (binder.bound s)) →
      ∃ k, bvVar decl.args k = i ∧ k ∈ depsAt st' i := by
    intro i hi ⟨s, hs⟩
    obtain ⟨b, _, hnode⟩ := hL.nodes i hi
    have hnode' := getElem?_prefix hx.store hnode
    obtain ⟨k, hk, hkd⟩ := var_node_dep hfin.store hnode' hs
    exact ⟨k, hk, by simp [depsAt, State.ty, hnode', Node.ty, hkd]⟩
  have hdisj : ∀ {A B : Finset ℕ} {k : ℕ}, Disjoint A B → k ∈ A → k ∈ B → False :=
    fun hAB hA hB => Finset.disjoint_left.1 hAB hA hB
  -- the renaming
  have hρ : Renaming Δ Γ σ' r := by
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i j hi hj hij => ?_, fun u s vs hu x hx => ?_⟩
    · by_cases hin : i < n
      · rw [hrlow i hin, hrlow' i hin]
      · obtain ⟨z, hz, hrz, _⟩ := hrhigh (i - n) (by omega)
        rw [Nat.add_sub_cancel' (Nat.le_of_not_lt hin)] at hz hrz
        rw [hz, hrz]
    · by_cases hin : i < n
      · rw [hrlow' i hin, hΓ, hΔ, ctxOf_getElem_binder D (List.getElem?_eq_getElem hin),
          ctxOf_getElem_binder ds (List.getElem?_eq_getElem hin)]
      · obtain ⟨z, _, hrz, hΓz⟩ := hrhigh (i - n) (by omega)
        rw [Nat.add_sub_cancel' (Nat.le_of_not_lt hin)] at hrz
        rw [hrz, hΓz, hΔ]
        have := ctxOf_getElem_dummy decl.args (List.getElem?_eq_getElem (show i - n < ds.length by omega))
        rw [Nat.add_sub_cancel' (Nat.le_of_not_lt hin)] at this
        rw [this]
    · -- distinct variables: binders are fixed, dummies are fresh
      have key : ∀ i j, i < n → n ≤ j → j < Δ.length → r i = r j → False := by
        intro i j hi hnj hj hij
        obtain ⟨k, hk, hkd⟩ := hdummy_dep (j - n) (by omega)
        rw [Nat.add_sub_cancel' hnj] at hk
        obtain ⟨z, _, hrz, hΓz⟩ := hrhigh (j - n) (by omega)
        rw [Nat.add_sub_cancel' hnj] at hrz
        rw [hrlow' i hi] at hij
        have hbi : ∃ s, Γ[i]? = some (binder.bound s) := ⟨_, by rw [hij, hrz]; exact hΓz⟩
        obtain ⟨k', hk', hkd'⟩ := hbinder_dep i hi hbi
        have hkk : k = k' := bvVar_injective _ (by rw [hk, hk', hij])
        subst hkk
        have hfresh := (hdn2 (j - n) (by omega)).1 (i, false) (by simp [argHeap, hi]) rfl
        exact hdisj hfresh hkd hkd'
      by_cases hin : i < n <;> by_cases hjn : j < n
      · rw [hrlow' i hin, hrlow' j hjn] at hij; exact hij
      · exact (key i j hin (Nat.le_of_not_lt hjn) hj hij).elim
      · exact (key j i hjn (Nat.le_of_not_lt hin) hi hij.symm).elim
      · by_contra hne
        obtain ⟨k, hk, hkd⟩ := hdummy_dep (i - n) (by omega)
        obtain ⟨k', hk', hkd'⟩ := hdummy_dep (j - n) (by omega)
        rw [Nat.add_sub_cancel' (Nat.le_of_not_lt hin)] at hk
        rw [Nat.add_sub_cancel' (Nat.le_of_not_lt hjn)] at hk'
        have hkk : k = k' := bvVar_injective _ (by rw [hk, hk', hij])
        subst hkk
        rcases Nat.lt_or_gt_of_ne (show i - n ≠ j - n by omega) with hlt | hlt
        · exact hdisj ((hdn2 (j - n) (by omega)).2 (i - n) hlt) hkd' hkd
        · exact hdisj ((hdn2 (i - n) (by omega)).2 (j - n) hlt) hkd hkd'
    · -- a regular binder depends on binders
      have hul : u < n := by
        by_contra hun
        have hd : u - n < ds.length := by
          have := (List.getElem?_eq_some_iff.1 hu).1
          omega
        have := ctxOf_getElem_dummy decl.args (List.getElem?_eq_getElem hd)
        rw [Nat.add_sub_cancel' (Nat.le_of_not_lt hun), hu] at this
        cases this
      rw [hΔ, ctxOf_getElem_binder ds (List.getElem?_eq_getElem hul)] at hu
      cases hb : decl.args[u].bound with
      | true => rw [toMm0_bound hb] at hu; cases hu
      | false =>
        rw [toMm0_reg hb] at hu
        simp only [Option.some.injEq, binder.reg.injEq] at hu
        obtain ⟨_, rfl⟩ := hu
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
        have hkl := lt_of_lt_of_le ((hbwf u _ (List.getElem?_eq_getElem hul)).2 hb k hk)
          (countBefore_le_nb _ (le_of_lt hul))
        exact hrlow' _ (bvVar_lt_of_lt hkl)
  -- the free variable, carried to the value's node
  have hΔreg := regDepsBound_ctxOf hbwf ds
  obtain ⟨s0, hs0⟩ := free_bound hu hr hΔreg hvok hxf
  have hxl : x < Δ.length := (List.getElem?_eq_some_iff.1 hs0).1
  have hfree := free_rename hρ hxl (by rw [← hσ'len]; exact hvl) hxf
  rw [← hsx] at hfree
  have hΓrx : Γ[r x]? = some (binder.bound s0) := by rw [hρ.ctx x hxl, hs0]
  obtain ⟨k, hk, hkx⟩ := bvVar_of_bound hΓrx
  obtain ⟨n0, hn0, rfl⟩ := State.ty_some hty
  have hkdeps : k ∈ n0.ty.deps := ((hfin.store.nodes e n0 hn0).deps k).2 ⟨hk, by unfold Dep; simp only [ite_true]; rw [hkx]; exact hfree⟩
  have hkret := hdeps hkdeps
  have hknb := hnb k hkret
  have hrxn : r x < n := by rw [← hkx]; exact bvVar_lt_of_lt hknb
  have hxn : x < n := by
    by_contra hxn
    have := hρ.inj (r x) x (by rw [hΔlen]; omega) hxl (hrlow' (r x) hrxn)
    rw [this] at hrxn
    exact hxn hrxn
  rw [hrlow' x hxn] at hkx
  rw [← hkx]
  exact Finset.mem_image_of_mem _ hkret

/-! ### A theorem statement -/

/-- The hypotheses so far have provable sorts. -/
def HypsProvable (c : Ctx) (st : State) : Prop :=
  ∀ p ∈ st.hyps, ∃ ty sd, st.ty p = some ty ∧ c.sorts[ty.sort]? = some sd ∧ sd.provable = true

theorem step_hypsProvable {c : Ctx} {cmd : ProofCmd} {st st' : State} (hs : Step c cmd st st')
    (h : HypsProvable c st) : HypsProvable c st' := by
  have hx := step_ext hs
  have hlift : ∀ p, (∃ ty sd, st.ty p = some ty ∧ c.sorts[ty.sort]? = some sd ∧ sd.provable = true) →
      ∃ ty sd, st'.ty p = some ty ∧ c.sorts[ty.sort]? = some sd ∧ sd.provable = true := by
    rintro p ⟨ty, sd, hty, hsd, hprov⟩
    have hty' : st'.ty p = (st.withStore st'.store).ty p := rfl
    exact ⟨ty, sd, by rw [hty']; exact ty_prefix hx.store hty, hsd, hprov⟩
  cases hs
  case hyp e S ty sd hdef hsd hprov hstk hty =>
    intro p hp
    simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact hlift p (h p hp)
    · exact hlift p ⟨ty, sd, hty, hsd, hprov⟩
  all_goals exact fun p hp => hlift p (h p hp)

theorem run_hypsProvable {c : Ctx} : ∀ {cmds : List ProofCmd} {st st' : State}, Run c cmds st st' →
    HypsProvable c st → HypsProvable c st'
  | _, _, _, Run.nil _, h => h
  | _, _, _, Run.cons _ _ _ _ _ hs hr, h => run_hypsProvable hr (step_hypsProvable hs h)

theorem thm_stmt_wf {E : env} {c : Ctx} {allTerms : List TermDecl} (hE : EnvHas E c allTerms)
    (hdef : c.isDef = false) {decl : ThmDecl} {isAx : Bool} {body : List ProofCmd}
    (h : ThmOk c decl isAx body) {concl : sexpr} {hl : List sexpr}
    (hdec : decodeThm allTerms decl.args.length decl.unify = some (concl, hl)) :
    axiom_ok E (decl.args.map (Binder.toMm0 decl.args)) hl concl := by
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
  rw [argsUheap_eq hL hx.heap] at hU
  obtain ⟨concl', hl', hdec', hsx, hvl, hall⟩ := unify_end hfin.store.wf hT' hE.terms_prefix hU
  simp only [List.length_range] at hdec' hvl hall
  rw [hdec] at hdec'
  simp only [Option.some.injEq, Prod.mk.injEq] at hdec'
  obtain ⟨rfl, rfl⟩ := hdec'
  have hctx0 := ctxOk_loaded hE hL
  have hargs : decl.args.map (Binder.toMm0 decl.args) = ctxOf decl.args [] := by simp [ctxOf]
  have hsplit : ctxOf decl.args D = ctxOf decl.args [] ++ D.map binder.bound := by simp [ctxOf]
  have hlen0 : (ctxOf decl.args []).length = decl.args.length := by simp [ctxOf_length]
  -- a node of the final store whose expression has variables below the binders
  have hnode : ∀ p ty', st'.ty p = some ty' → (∃ sd', c.sorts[ty'.sort]? = some sd' ∧ sd'.provable = true) →
      sexpr.VarsLt (toSexpr st'.store p) decl.args.length → sexpr.ok_prov E (ctxOf decl.args []) (toSexpr st'.store p) := by
    intro p ty' hty' ⟨sd', hsd', hprov'⟩ hvl'
    obtain ⟨n0, hn0, rfl⟩ := State.ty_some hty'
    have hok := (hfin.store.nodes p n0 hn0).ok
    rw [hsplit] at hok
    exact ⟨n0.ty.sort, sd', ok'_shrink (by rw [hlen0]; exact hvl') hok, hE.sorts _ _ hsd', hprov'⟩
  have hHP := run_hypsProvable hrun (by intro p hp; rw [hL.hyps] at hp; simp at hp)
  rw [hargs]
  refine ⟨hctx0, fun x hx' => ?_⟩
  have hid : (List.range decl.args.length).map (toSexpr st'.store) = (List.range decl.args.length).map sexpr.var :=
    range_map_toSexpr hL hx.store
  rcases List.mem_cons.1 hx' with rfl | hxh
  · have hxe : toSexpr st'.store e = x := by rw [hsx, hid, subst_id_of_varsLt hvl]
    rw [← hxe]
    exact hnode e ty hty ⟨sd, hsd, hprov⟩ (by rw [hxe]; exact hvl)
  · obtain ⟨p, hp, hph⟩ := forall₂_mem_right hall x hxh
    have hpx : toSexpr st'.store p = x := by rw [hph.1, hid, subst_id_of_varsLt hph.2]
    obtain ⟨ty', sd', hty', hsd', hprov'⟩ := hHP p (List.mem_reverse.1 hp)
    rw [← hpx]
    exact hnode p ty' hty' ⟨sd', hsd', hprov'⟩ (by rw [hpx]; exact hph.2)

end Verifier
