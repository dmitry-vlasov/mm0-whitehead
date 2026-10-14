/-
Every command keeps the stack invariant (milestone V3, part f): `Cong`, `Unfold` and
`Thm` in lemmas of their own, the rest in `step_sound`.
-/
import Verifier.World

namespace Verifier

open mm0
open Whitehead.Mmb (ProofCmd UnifyCmd)

variable {W : World} {c : Ctx} {allTerms : List TermDecl} {bs : List Binder} {D : List ℕ}

theorem lift_x (hW : WorldOk W c allTerms bs D) {store : List Node} (hwf : StoreWF store) (hpre : store <+: W.store)
    {p : ℕ} (hp : p < store.length) : W.x p = toSexpr store p :=
  toSexpr_prefix hwf hpre hp

theorem forall₂_get {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) {i : ℕ}
    (h₁ : i < l₁.length) (h₂ : i < l₂.length) : R l₁[i] l₂[i] := by
  have := (List.forall₂_iff_get.1 h).2 i h₁ h₂
  simpa using this

/-! ### `Cong` -/

theorem cong_ob (hW : WorldOk W c allTerms bs D) {store : List Node} (hpre : store <+: W.store)
    {e1 e2 : ℕ} {ty1 ty2 : Ty} {t : ℕ} {args1 args2 : List ℕ}
    (hn1 : store[e1]? = some (Node.app ty1 t args1)) (hn2 : store[e2]? = some (Node.app ty2 t args2))
    (hall : ∀ i (h1 : i < args1.length) (h2 : i < args2.length), ObTrue W args1[i] args2[i]) : ObTrue W e1 e2 := by
  have hu := hW.env.termsUnique
  have hn1f := getElem?_prefix hpre hn1
  have hn2f := getElem?_prefix hpre hn2
  have hx1 : W.x e1 = sexpr.app t (args1.map W.x) := toSexpr_app hW.store.wf hn1f
  have hx2 : W.x e2 = sexpr.app t (args2.map W.x) := toSexpr_app hW.store.wf hn2f
  have hok1 := hW.ok_node hn1f
  have hok2 := hW.ok_node hn2f
  rw [hx1] at hok1
  rw [hx2] at hok2
  obtain ⟨bis1, ret1, o1, hget1, hs1, hA⟩ := ok_app_inv hok1
  obtain ⟨bis2, ret2, o2, hget2, hs2, hB⟩ := ok_app_inv hok2
  obtain ⟨hbis, hret⟩ := hu _ _ _ _ _ _ _ hget2 hget1
  subst hbis hret
  have hlA := hA.length_eq
  have hlB := hB.length_eq
  have hconv : conv' W.E W.Γ (sexpr.app t (args1.map W.x)) (sexpr.app t (args2.map W.x)) [] ret2.1 := by
    refine conv'_app'_cong bis2 _ _ _ _ hlA hlB (fun i h1 h2 hb => ?_) (by rw [List.append_nil]; exact conv'.refl (sexpr.ok'.term hget1))
    have ha := forall₂_get hA h1 hb
    have hb' := forall₂_get hB h2 hb
    simp only [List.length_map] at h1 h2
    obtain ⟨s, hc, hoka, _⟩ := hall i h1 h2
    simp only [List.getElem_map] at ha hb' ⊢
    have := ok_bi_sort hu ha hoka
    subst this
    exact ⟨ha, hb', hc⟩
  refine ⟨ret2.1, ?_, ?_, ?_⟩
  · rw [hx1, hx2]; exact hconv
  · rw [hx1]; rw [hs1] at hok1; exact hok1
  · rw [hx2]; rw [hs2] at hok2; exact hok2

/-! ### `Unfold` -/

def getVar : sexpr → ℕ
  | .var z => z
  | _ => 0

theorem unfold_ob (hW : WorldOk W c allTerms bs D) {st : State} (hwf : StoreWF st.store) (hT : StoreTerms c st.store)
    (hpre : st.store <+: W.store) {e e2 e' : ℕ} {ty : Ty} {t : ℕ} {args : List ℕ} {decl : TermDecl}
    {us : List UnifyCmd} {S : List El}
    (hn : st.store[e]? = some (Node.app ty t args)) (hd : c.terms[t]? = some decl) (hus : decl.defn = some us)
    (hU : Unify c st .defn (args.map fun p => (p, false)) us [e2] S [] S [])
    (he2 : e2 < st.store.length) (hob : ObTrue W e2 e') : ObTrue W e e' := by
  have hu := hW.env.termsUnique
  obtain ⟨v, ds', σ', hdec, hσpre, hσlen, hdum, hsx, -, -⟩ := unify_defn hwf hT hW.env.terms_prefix hU
  obtain ⟨d0, hd0, hl0⟩ := hT e ty t args hn
  rw [hd] at hd0
  cases hd0
  rw [hl0] at hdec hσlen hdum
  obtain ⟨o, hget, hdefn⟩ := hW.env.terms t decl hd
  obtain ⟨v', ds'', hdec', ho⟩ := hdefn us hus
  rw [hdec] at hdec'
  simp only [Option.some.injEq, Prod.mk.injEq] at hdec'
  obtain ⟨rfl, rfl⟩ := hdec'
  subst ho
  have hvok := hW.env.defs_ok t decl us v ds' hd hus hdec
  have hargs_lt : ∀ q ∈ args, q < e := hwf e ty t args hn
  have he : e < st.store.length := (List.getElem?_eq_some_iff.1 hn).1
  have hnf := getElem?_prefix hpre hn
  have hxe : W.x e = sexpr.app t (args.map W.x) := toSexpr_app hW.store.wf hnf
  have hoke := hW.ok_node hnf
  rw [hxe] at hoke
  obtain ⟨bis, ret, o', hget', hs, hes⟩ := ok_app_inv hoke
  obtain ⟨hbis, hret⟩ := hu _ _ _ _ _ _ _ hget' hget
  subst hbis hret
  have hsort : (Node.app ty t args).ty.sort = decl.ret.sort := hs
  rw [hsort] at hoke
  -- the substitution: the arguments, then the dummies' variables
  have hmap : args.map (toSexpr st.store) = args.map W.x :=
    List.map_congr_left fun q hq => (lift_x hW hwf hpre (lt_trans (hargs_lt q hq) he)).symm
  obtain ⟨tl, htl⟩ := hσpre
  rw [hmap] at htl
  subst htl
  have hn' : (args.map W.x).length = decl.args.length := by simp [hl0]
  have htllen : tl.length = ds'.length := by
    simp only [List.length_append, List.length_map] at hσlen
    omega
  have hdummy : ∀ j (hj : j < tl.length), ∃ z, tl[j] = sexpr.var z ∧ W.Γ[z]? = some (binder.bound (ds'[j]'(by omega))) := by
    intro j hj
    obtain ⟨v0, ty0, p0, hv0, hp0, hb0, hs0⟩ := hdum j (ds'[j]'(by omega)) (List.getElem?_eq_getElem _)
    rw [List.getElem?_append_right (by simp [hl0]), List.length_map, hl0, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj] at hv0
    simp only [Option.some.injEq] at hv0
    refine ⟨v0, hv0, ?_⟩
    have hp0f := getElem?_prefix hpre hp0
    obtain ⟨v1, s1, hv1, hΓ⟩ := (hW.node hp0f).bound.1 hb0
    simp only [Node.var.injEq] at hv1
    obtain ⟨_, rfl⟩ := hv1
    have hok0 := hW.ok_node hp0f
    rw [show W.x p0 = sexpr.var v0 from toSexpr_var hp0f] at hok0
    obtain ⟨bi, hbi, _, hbs⟩ := ok'_var_inv hok0
    rw [hW.ctx] at hbi
    rw [hΓ] at hbi
    simp only [Option.some.injEq] at hbi
    subst hbi
    simp only [binder.sort] at hbs
    rw [hW.ctx, hΓ]
    have hs1 : s1 = ds'[j]'(by omega) := by rw [← hbs]; exact hs0
    rw [hs1]
  set zs := tl.map getVar with hzsdef
  have htlz : tl = zs.map sexpr.var := by
    apply List.ext_getElem (by simp [hzsdef])
    intro j h1 h2
    obtain ⟨z, hz, _⟩ := hdummy j h1
    simp [hzsdef, hz, getVar]
  have hzs : List.Forall₂ (fun y z => W.Γ[z]? = some (binder.bound y)) ds' zs := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp [hzsdef, htllen], fun j h1 h2 => ?_⟩
    have hj : j < tl.length := by omega
    obtain ⟨z, hz, hΓ⟩ := hdummy j hj
    simp only [List.get_eq_getElem, hzsdef, List.getElem_map, hz, getVar]
    exact hΓ
  -- the substitution fits the def's context
  have hfit : ∀ (i : ℕ) (bi : binder), (ctxOf decl.args ds')[i]? = some bi →
      sexpr.ok_bi W.E W.Γ ((args.map W.x ++ tl).getD i default) bi := by
    intro i bi hi
    by_cases hia : i < decl.args.length
    · rw [ctxOf_getElem_binder ds' (List.getElem?_eq_getElem hia)] at hi
      simp only [Option.some.injEq] at hi
      subst hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hn']; exact hia)]
      have hia' : i < (args.map W.x).length := by rw [hn']; exact hia
      rw [List.getElem?_eq_getElem hia']
      have := forall₂_get hes hia' (by simpa using hia)
      simpa using this
    · have hil : i < decl.args.length + ds'.length := by
        have := (List.getElem?_eq_some_iff.1 hi).1
        rwa [ctxOf_length] at this
      have hj : i - decl.args.length < ds'.length := by omega
      have hΔ := ctxOf_getElem_dummy decl.args (List.getElem?_eq_getElem hj)
      rw [Nat.add_sub_cancel' (Nat.le_of_not_lt hia), hi] at hΔ
      simp only [Option.some.injEq] at hΔ
      subst hΔ
      obtain ⟨z, hz, hΓ⟩ := hdummy (i - decl.args.length) (by omega)
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hn']; omega), hn',
        List.getElem?_eq_getElem (by omega), hz]
      exact ⟨z, rfl, hΓ⟩
  have hok2 := ok'_subst hfit hvok
  have hunf : conv' W.E W.Γ (sexpr.subst (args.map W.x ++ zs.map sexpr.var) v) (sexpr.app t (args.map W.x)) []
      decl.ret.sort := conv'.unfold hget hes hzs (conv'.refl hoke)
  rw [← htlz] at hunf
  have hx2 : W.x e2 = sexpr.subst (args.map W.x ++ tl) v := (lift_x hW hwf hpre he2).trans hsx
  obtain ⟨s, hc, hok2', hok'⟩ := hob
  rw [hx2] at hok2'
  have hs' : decl.ret.sort = s := ok_unique hu hok2 hok2'
  subst hs'
  refine ⟨decl.ret.sort, ?_, by rw [hxe]; exact hoke, hok'⟩
  rw [hxe]
  rw [hx2] at hc
  exact conv'.trans (conv'.symm hunf) hc

/-! ### `Thm` -/

theorem thm_sound (hW : WorldOk W c allTerms bs D) {st : State} (hwf : StoreWF st.store) (hT : StoreTerms c st.store)
    (hpre : st.store <+: W.store) (hdef : c.isDef = false) {t : ℕ} {decl : ThmDecl} {e : ℕ} {args : List ℕ}
    {S₁ S₂ S₃ : List El} (hdecl : c.thms[t]? = some decl) (hstk : st.stack = El.expr e :: S₁)
    (hpop : popArgs decl.args.length S₁ args S₂) (hargs : argsOk st decl.args args)
    (hdis : thmDisjoint st decl.args args [] [])
    (hU : Unify c st .thm (args.map fun p => (p, false)) decl.unify [e] S₂ [] S₃ [])
    (hS : SOk W st.store.length st.stack) :
    e < st.store.length ∧ proof W.E W.Γ W.Hs (W.x e) ∧ SOk W st.store.length S₃ := by
  rw [hstk] at hS
  have he : e < st.store.length := hS.1
  have hS₁ := SOk.tail_of_not_ob hS (fun a b h => by cases h)
  obtain ⟨hlen, hS₁eq⟩ := popArgs_spec hpop
  rw [hS₁eq] at hS₁
  obtain ⟨hargs_lt, hS₂⟩ := SOk.drop_exprs args.reverse hS₁
  obtain ⟨concl, hl, ps, hdec, hsx, hS₂eq, hall⟩ := unify_thm hwf hT hW.env.terms_prefix hU
  rw [hS₂eq] at hS₂
  obtain ⟨hps, hS₃⟩ := SOk.drop_proofs ps hS₂
  obtain ⟨concl', hs', hdec', hget⟩ := hW.env.thms t decl hdecl
  rw [hlen] at hdec
  rw [hdec] at hdec'
  simp only [Option.some.injEq, Prod.mk.injEq] at hdec'
  obtain ⟨rfl, rfl⟩ := hdec'
  -- the substitution in the final world
  have hσ : args.map (toSexpr st.store) = args.map W.x :=
    List.map_congr_left fun q hq => (lift_x hW hwf hpre (hargs_lt q (List.mem_reverse.2 hq))).symm
  set st₀ := st.withStore W.store
  have hst₀ : StoreOk W.E bs D false st₀.store := by
    have := hW.store
    rw [hdef] at this
    exact this
  have hok := argsOk_forall₂ hst₀ (argsOk_prefix hpre hargs)
  have hsafe := safe_subst_of hst₀ (argsOk_prefix hpre hargs) (thmDisjoint_prefix hpre hdis)
  change List.Forall₂ _ (args.map W.x) _ at hok
  change safe_subst _ _ (args.map W.x) at hsafe
  rw [← hW.ctx] at hok hsafe
  have hxe : W.x e = sexpr.subst (args.map W.x) concl := by
    rw [lift_x hW hwf hpre he, hsx, hσ]
  refine ⟨he, ?_, hS₃⟩
  rw [hxe]
  refine proof.thm hget hok hsafe fun h hh => ?_
  obtain ⟨p, hp, hph⟩ := forall₂_mem_right hall h hh
  obtain ⟨hpl, hpp⟩ := hps p hp
  rw [← hσ, ← hph, ← lift_x hW hwf hpre hpl]
  exact hpp

end Verifier
