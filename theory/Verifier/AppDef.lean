/-
An application in a definition (milestone V3, part b): its dependencies are the free
variables, `Free` of `mm0.mm0` as `sexpr.free` has it.
-/
import Verifier.NewNodes

namespace Verifier

open mm0

theorem bvVar_lt_iff (bs : List Binder) (ds : List ℕ) (k : ℕ) :
    bvVar bs k < bs.length + ds.length ↔ k < nbv bs ds := by
  constructor
  · intro h
    by_contra hk
    rw [bvVar_of_ge (by unfold nbv at hk; omega)] at h
    unfold nbv at hk
    omega
  · exact bvVar_lt

/-- The dependency set of the argument at a bound binder of the term is the number of
the variable substituted for it. -/
theorem mem_argDeps_iff {E : env} {bs : List Binder} {ds : List ℕ} {isDef : Bool} {st : State}
    (hst : StoreOk E bs ds isDef st.store) {tbs : List Binder} {args : List ℕ} (hargs : argsOk st tbs args)
    {m : ℕ} (hm : m < (boundNumbers tbs).length) (k : ℕ) :
    k ∈ argDeps tbs (args.map fun p => (st.ty p).getD ⟨0, false, ∅⟩) m ↔
      (args.map (toSexpr st.store))[bvVar tbs m]? = some (sexpr.var (bvVar bs k)) := by
  have hlen := argsOk_length hargs
  have hj : bvVar tbs m < tbs.length := bvVar_lt_of_lt hm
  have hjb : isBoundAt tbs (bvVar tbs m) := by rw [bvVar_of_lt hm]; exact boundNumbers_bound hm
  obtain ⟨b, hb, hbb⟩ := isBoundAt_iff.1 hjb
  have hja : bvVar tbs m < args.length := by omega
  obtain ⟨ty, hty, _, hbound⟩ := argsOk_get hargs _ b args[bvVar tbs m] hb (List.getElem?_eq_getElem hja)
  obtain ⟨n, hn, rfl⟩ := State.ty_some hty
  have hok := hst.nodes _ n hn
  obtain ⟨v, s, hnv, hv⟩ := hok.bound.1 (hbound hbb)
  rw [hnv] at hn
  have hsx := toSexpr_var hn
  have hL : k ∈ argDeps tbs (args.map fun p => (st.ty p).getD ⟨0, false, ∅⟩) m ↔ k < nbv bs ds ∧ v = bvVar bs k := by
    unfold argDeps
    rw [List.getElem?_map, List.getElem?_eq_getElem hja]
    simp only [Option.map_some, Option.getD_some]
    rw [hty]
    simp only [Option.getD_some]
    rw [hok.deps k, hsx, dep_var, has_var_var_bound hv]
  have hR : (args.map (toSexpr st.store))[bvVar tbs m]? = some (sexpr.var (bvVar bs k)) ↔ v = bvVar bs k := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hja]
    simp only [Option.map_some]
    rw [hsx]
    simp
  rw [hL, hR]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    refine ⟨?_, h⟩
    have hvl : v < bs.length + ds.length := by
      have := hok.varsLt
      rw [hsx] at this
      exact this
    rw [h] at hvl
    exact (bvVar_lt_iff bs ds k).1 hvl

theorem nodeOk_app_def {E : env} {bs : List Binder} {ds : List ℕ} {st : State}
    (hst : StoreOk E bs ds true st.store) {c : Ctx} {allTerms : List TermDecl} (hE : EnvHas E c allTerms)
    {t : ℕ} {d : TermDecl} (hd : c.terms[t]? = some d) {args : List ℕ} (hargs : argsOk st d.args args) :
    NodeOk E bs ds true
      (st.store ++ [Node.app ⟨d.ret.sort, false, appDeps true d.args d.ret (args.map fun p => (st.ty p).getD ⟨0, false, ∅⟩)⟩ t args])
      st.store.length
      (Node.app ⟨d.ret.sort, false, appDeps true d.args d.ret (args.map fun p => (st.ty p).getD ⟨0, false, ∅⟩)⟩ t args) := by
  set tys := args.map fun p => (st.ty p).getD ⟨0, false, ∅⟩ with htys
  set ty : Ty := ⟨d.ret.sort, false, appDeps true d.args d.ret tys⟩ with hty
  have hlen := argsOk_length hargs
  have hvalid : ∀ p ∈ args, p < st.store.length := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
    obtain ⟨ty', hty', _, _⟩ := argsOk_get hargs i d.args[i] args[i] (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem hi)
    obtain ⟨n, hn, _⟩ := State.ty_some hty'
    exact (List.getElem?_eq_some_iff.1 hn).1
  have hwf' := hst.wf.append_app ty t hvalid
  have hn : (st.store ++ [Node.app ty t args])[st.store.length]? = some (Node.app ty t args) := List.getElem?_concat_length
  have hsx := toSexpr_app hwf' hn
  have hmap : args.map (toSexpr (st.store ++ [Node.app ty t args])) = args.map (toSexpr st.store) :=
    List.map_congr_left fun p hp => toSexpr_append hst.wf _ (hvalid p hp)
  set es := args.map (toSexpr st.store) with hes
  obtain ⟨o, hget, _⟩ := hE.terms t d hd
  obtain ⟨hbwf, hret⟩ := hE.terms_wf t d hd
  refine ⟨?_, ?_, ?_⟩
  · rw [hsx, hmap]
    exact ok_app hget (argsOk_forall₂ hst hargs)
  · constructor
    · intro h
      have hb : ty.bound = false := rfl
      change ty.bound = true at h
      rw [hb] at h
      exact absurd h Bool.false_ne_true
    · rintro ⟨v, s, h, _⟩
      cases h
  · intro k
    show k ∈ appDeps true d.args d.ret tys ↔ _
    rw [hsx, hmap]
    unfold Dep
    simp only [ite_true]
    rw [mem_appDeps_def, free_app]
    -- the term's declaration, unique
    have huniq : ∀ a r o', E.get_term t a r o' → a = d.args.map (Binder.toMm0 d.args) ∧ r = depTypeOf d.args d.ret := by
      intro a r o' h
      obtain ⟨d', hd', ha, hr⟩ := hE.terms_unique t a r o' h
      rw [hd] at hd'
      obtain rfl := Option.some.inj hd'
      exact ⟨ha, hr⟩
    -- an argument's dependency set, for a bound binder of the term
    have hbd : ∀ m, m < (boundNumbers d.args).length → ∀ k,
        (k ∈ argDeps d.args tys m ↔ es[bvVar d.args m]? = some (sexpr.var (bvVar bs k))) :=
      fun m hm k => mem_argDeps_iff hst hargs hm k
    -- the arguments' nodes
    have hnode : ∀ i, (hi : i < d.args.length) → ∃ n, st.store[args[i]'(by omega)]? = some n ∧
        tys[i]? = some n.ty ∧ es[i]? = some (toSexpr st.store (args[i]'(by omega))) := by
      intro i hi
      obtain ⟨ty', hty', _, _⟩ := argsOk_get hargs i d.args[i] args[i] (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem (by omega))
      obtain ⟨n, hn, rfl⟩ := State.ty_some hty'
      refine ⟨n, hn, ?_, ?_⟩
      · rw [htys, List.getElem?_map, List.getElem?_eq_getElem (by omega)]
        simp only [Option.map_some, Option.some.injEq]
        rw [hty']
        rfl
      · rw [hes, List.getElem?_map, List.getElem?_eq_getElem (by omega)]
        rfl
    constructor
    · rintro (⟨i, hi, hreg, hk, hnot⟩ | ⟨m, hm, hk⟩)
      · obtain ⟨n, hn, htyi, hesi⟩ := hnode i hi
        rw [htyi] at hk
        simp only [Option.map_some, Option.getD_some] at hk
        have hok := hst.nodes _ n hn
        obtain ⟨hlt, hdep⟩ := (hok.deps k).1 hk
        unfold Dep at hdep
        simp only [ite_true] at hdep
        refine ⟨hlt, _, _, _, o, hget, Or.inl ⟨i, _, Binder.toMm0 d.args (d.args[i]'hi), hesi, ?_, hdep, ?_⟩⟩
        · rw [List.getElem?_map, List.getElem?_eq_getElem hi]
          rfl
        · obtain ⟨b, hb, hbb⟩ : ∃ b, d.args[i]? = some b ∧ b.bound = false := by
            refine ⟨d.args[i], List.getElem?_eq_getElem hi, ?_⟩
            have := (not_isBoundAt_iff hi).1 hreg
            rw [List.getElem?_eq_getElem hi] at this
            simpa using this
          rw [List.getElem?_eq_getElem hi] at hb
          simp only [Option.some.injEq] at hb
          subst hb
          refine ⟨d.args[i].sort, d.args[i].deps.image (bvVar d.args), toMm0_reg hbb, ?_⟩
          rintro ⟨u, hu, hesu⟩
          obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hu
          have hmlt : m < (boundNumbers d.args).length :=
            lt_of_lt_of_le ((hbwf i _ (List.getElem?_eq_getElem hi)).2 hbb m hm) (countBefore_le_nb _ (le_of_lt hi))
          have hdi : m ∈ (d.args[i]?.map fun b : Binder => b.deps).getD ∅ := by
            rw [List.getElem?_eq_getElem hi]
            simpa using hm
          exact hnot m hdi ((hbd m hmlt k).2 hesu)
      · have hmlt := hret m hm
        have hesu := (hbd m hmlt k).1 hk
        refine ⟨?_, _, _, _, o, hget, Or.inr ⟨bvVar d.args m, Finset.mem_image_of_mem _ hm, hesu⟩⟩
        -- `k` is below the number of bound variables: the variable is in the store
        have hj : bvVar d.args m < d.args.length := bvVar_lt_of_lt hmlt
        obtain ⟨n, hn, _, hesi⟩ := hnode _ hj
        rw [hesi] at hesu
        simp only [Option.some.injEq] at hesu
        have hok := hst.nodes _ n hn
        have hvl := hok.varsLt
        rw [hesu] at hvl
        exact (bvVar_lt_iff bs ds k).1 hvl
    · rintro ⟨hlt, a, r, rs, o', hget', h⟩
      obtain ⟨rfl, hr⟩ := huniq a (r, rs) o' hget'
      simp only [depTypeOf, Prod.mk.injEq] at hr
      obtain ⟨_, rfl⟩ := hr
      rcases h with ⟨n, e, b, hen, hbn, hfree, hmf⟩ | ⟨u, hu, hesu⟩
      · left
        have hn : n < d.args.length := by
          have := (List.getElem?_eq_some_iff.1 hbn).1
          simpa using this
        obtain ⟨nd, hnd, htyn, hesn⟩ := hnode n hn
        rw [hesn] at hen
        simp only [Option.some.injEq] at hen
        subst hen
        rw [List.getElem?_map, List.getElem?_eq_getElem hn] at hbn
        simp only [Option.map_some, Option.some.injEq] at hbn
        subst hbn
        obtain ⟨s', vs, hbeq, hnot⟩ := hmf
        have hreg : d.args[n].bound = false := by
          by_contra hbb
          rw [toMm0_bound (by simpa using hbb)] at hbeq
          cases hbeq
        refine ⟨n, hn, (not_isBoundAt_iff hn).2 (by rw [List.getElem?_eq_getElem hn]; simp [hreg]), ?_, ?_⟩
        · rw [htyn]
          simp only [Option.map_some, Option.getD_some]
          have hok := hst.nodes _ nd hnd
          refine (hok.deps k).2 ⟨hlt, ?_⟩
          unfold Dep
          simp only [ite_true]
          exact hfree
        · intro m hm hk
          rw [List.getElem?_eq_getElem hn] at hm
          simp only [Option.map_some, Option.getD_some] at hm
          have hmlt : m < (boundNumbers d.args).length :=
            lt_of_lt_of_le ((hbwf n _ (List.getElem?_eq_getElem hn)).2 hreg m hm) (countBefore_le_nb _ (le_of_lt hn))
          rw [toMm0_reg hreg] at hbeq
          simp only [binder.reg.injEq] at hbeq
          obtain ⟨_, rfl⟩ := hbeq
          exact hnot ⟨bvVar d.args m, Finset.mem_image_of_mem _ hm, (hbd m hmlt k).1 hk⟩
      · right
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hu
        exact ⟨m, hm, (hbd m (hret m hm) k).2 hesu⟩

end Verifier
