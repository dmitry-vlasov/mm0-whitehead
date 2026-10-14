/-
The nodes the commands create (milestone V3, part b): a binder's variable, a dummy, and
an application in an axiom or theorem, each with the meaning of its type word.
-/
import Verifier.StoreStep

namespace Verifier

open mm0

theorem toMm0_sort (bs : List Binder) (b : Binder) : (Binder.toMm0 bs b).sort = b.sort := by
  unfold Binder.toMm0
  cases b.bound <;> simp [binder.sort]

/-! ### A binder's variable -/

theorem nodeOk_binder {E : env} {bs : List Binder} (hwf : BindersWF bs) {isDef : Bool} {store : List Node}
    {i : ℕ} {b : Binder} (hb : bs[i]? = some b) (hn : store[i]? = some (Node.var (Ty.ofBinder b) i)) :
    NodeOk E bs [] isDef store i (Node.var (Ty.ofBinder b) i) := by
  have hi : i < bs.length := (List.getElem?_eq_some_iff.1 hb).1
  have hsx := toSexpr_var hn
  have hΓ := ctxOf_getElem_binder [] hb
  refine ⟨?_, ?_, ?_⟩
  · rw [hsx]
    show sexpr.ok' E _ (sexpr.var i) [] b.sort
    rw [← toMm0_sort bs b]
    exact sexpr.ok'.var hΓ
  · show b.bound = true ↔ _
    constructor
    · intro hbb
      exact ⟨i, b.sort, rfl, by rw [hΓ, toMm0_bound hbb]⟩
    · rintro ⟨v, s, hv, hvs⟩
      simp only [Node.var.injEq] at hv
      obtain ⟨_, hiv⟩ := hv
      subst hiv
      rw [hΓ] at hvs
      cases hbb : b.bound with
      | true => rfl
      | false =>
        rw [toMm0_reg hbb] at hvs
        simp at hvs
  · intro k
    show k ∈ b.deps ↔ _
    rw [hsx, dep_var]
    unfold nbv
    simp only [List.length_nil, Nat.add_zero]
    cases hbb : b.bound with
    | true =>
      rw [(hwf i b hb).1 hbb, Finset.mem_singleton, has_var_var_bound (by rw [hΓ, toMm0_bound hbb])]
      have hcb := bvVar_countBefore hi (isBoundAt_iff.2 ⟨b, hb, hbb⟩)
      constructor
      · rintro rfl
        exact ⟨countBefore_lt hi (isBoundAt_iff.2 ⟨b, hb, hbb⟩), hcb.symm⟩
      · rintro ⟨_, h⟩
        rw [← hcb] at h
        exact (bvVar_injective bs h).symm
    | false =>
      rw [has_var_var_reg (by rw [hΓ, toMm0_reg hbb])]
      constructor
      · intro hk
        refine ⟨?_, Finset.mem_image_of_mem _ hk⟩
        exact lt_of_lt_of_le ((hwf i b hb).2 hbb k hk) (countBefore_le_nb bs (le_of_lt hi))
      · rintro ⟨_, h⟩
        obtain ⟨k', hk', hkk⟩ := Finset.mem_image.1 h
        rw [bvVar_injective bs hkk] at hk'
        exact hk'

/-! ### A dummy -/

theorem nodeOk_dummy {E : env} {bs : List Binder} {ds : List ℕ} {isDef : Bool} {store : List Node} (s : ℕ) :
    NodeOk E bs (ds ++ [s]) isDef (store ++ [Node.var ⟨s, true, {nbv bs ds}⟩ (bs.length + ds.length)]) store.length
      (Node.var ⟨s, true, {nbv bs ds}⟩ (bs.length + ds.length)) := by
  have hn : (store ++ [Node.var ⟨s, true, {nbv bs ds}⟩ (bs.length + ds.length)])[store.length]? =
      some (Node.var ⟨s, true, {nbv bs ds}⟩ (bs.length + ds.length)) := List.getElem?_concat_length
  have hsx := toSexpr_var hn
  have hd : (ds ++ [s])[ds.length]? = some s := List.getElem?_concat_length
  have hΓ := ctxOf_getElem_dummy bs hd
  refine ⟨?_, ?_, ?_⟩
  · rw [hsx]
    exact sexpr.ok'.var hΓ
  · constructor
    · intro _
      exact ⟨bs.length + ds.length, s, rfl, hΓ⟩
    · intro _
      rfl
  · intro k
    rw [hsx, dep_var, has_var_var_bound hΓ]
    show k ∈ ({nbv bs ds} : Finset ℕ) ↔ _
    rw [Finset.mem_singleton]
    have hnbv : nbv bs (ds ++ [s]) = nbv bs ds + 1 := by
      unfold nbv
      rw [List.length_append, List.length_singleton]
      omega
    rw [hnbv]
    constructor
    · rintro rfl
      refine ⟨by omega, ?_⟩
      rw [bvVar_of_ge (by unfold nbv; omega)]
      unfold nbv
      omega
    · rintro ⟨hk, h⟩
      by_contra hne
      have hk' : k < nbv bs ds := by omega
      have := bvVar_lt (ds := ds) hk'
      omega

/-! ### An application in an axiom or theorem -/

/-- The types of the arguments, as `Step.term` reads them. -/
theorem tys_of_args {st : State} {tbs : List Binder} {args : List ℕ} (h : argsOk st tbs args) :
    ∀ ty ∈ args.map (fun p => (st.ty p).getD ⟨0, false, ∅⟩), ∃ p ∈ args, st.ty p = some ty := by
  intro ty hty
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hty
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
  have hlen := argsOk_length h
  obtain ⟨ty', hty', _, _⟩ := argsOk_get h i tbs[i] args[i] (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem hi)
  refine ⟨args[i], hp, ?_⟩
  rw [hty']
  rfl

theorem nodeOk_app_thm {E : env} {bs : List Binder} {ds : List ℕ} {st : State}
    (hst : StoreOk E bs ds false st.store) {c : Ctx} {allTerms : List TermDecl} (hE : EnvHas E c allTerms)
    {t : ℕ} {d : TermDecl} (hd : c.terms[t]? = some d) {args : List ℕ} (hargs : argsOk st d.args args) :
    NodeOk E bs ds false
      (st.store ++ [Node.app ⟨d.ret.sort, false, appDeps false d.args d.ret (args.map fun p => (st.ty p).getD ⟨0, false, ∅⟩)⟩ t args])
      st.store.length
      (Node.app ⟨d.ret.sort, false, appDeps false d.args d.ret (args.map fun p => (st.ty p).getD ⟨0, false, ∅⟩)⟩ t args) := by
  set ty : Ty := ⟨d.ret.sort, false, appDeps false d.args d.ret (args.map fun p => (st.ty p).getD ⟨0, false, ∅⟩)⟩ with hty
  have hvalid : ∀ p ∈ args, p < st.store.length := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
    have hlen := argsOk_length hargs
    obtain ⟨ty', hty', _, _⟩ := argsOk_get hargs i d.args[i] args[i] (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem hi)
    obtain ⟨n, hn, _⟩ := State.ty_some hty'
    exact (List.getElem?_eq_some_iff.1 hn).1
  have hwf' := hst.wf.append_app ty t hvalid
  have hn : (st.store ++ [Node.app ty t args])[st.store.length]? = some (Node.app ty t args) := List.getElem?_concat_length
  have hsx := toSexpr_app hwf' hn
  have hmap : args.map (toSexpr (st.store ++ [Node.app ty t args])) = args.map (toSexpr st.store) :=
    List.map_congr_left fun p hp => toSexpr_append hst.wf _ (hvalid p hp)
  obtain ⟨o, hget, _⟩ := hE.terms t d hd
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
    show k ∈ appDeps false d.args d.ret _ ↔ _
    rw [mem_appDeps_thm, hsx, hmap, dep_app_thm]
    constructor
    · rintro ⟨ty', hty', hk⟩
      obtain ⟨p, hp, hty''⟩ := tys_of_args hargs ty' hty'
      obtain ⟨n, hn, rfl⟩ := State.ty_some hty''
      have hok := hst.nodes p n hn
      obtain ⟨hlt, hdep⟩ := (hok.deps k).1 hk
      exact ⟨hlt, toSexpr st.store p, List.mem_map_of_mem hp, hdep⟩
    · rintro ⟨hlt, e, he, hdep⟩
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
      have hlen := argsOk_length hargs
      obtain ⟨ty', hty', _, _⟩ := argsOk_get hargs i d.args[i] args[i] (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem hi)
      obtain ⟨n, hn, rfl⟩ := State.ty_some hty'
      have hok := hst.nodes _ n hn
      refine ⟨n.ty, ?_, (hok.deps k).2 ⟨hlt, hdep⟩⟩
      refine List.mem_map.2 ⟨args[i], hp, ?_⟩
      rw [hty']
      rfl

end Verifier
