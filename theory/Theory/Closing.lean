/-
The closing of a proof (`docs/THEORY.md`, decision 8): every variable a valid tree
leaves becomes a distinct dummy of its sort, and the result is a proof of the
statement. The conditions on bound variables are kept because a condition fails only
when its name already occurs, and the dummies are fresh and distinct.
-/
import Theory.Deduction

namespace Theory

open PTree

theorem closing_f_of_mem {db : Database} {T : PTree} {v : Var} (h : v ∈ T.allVars db) :
    (T.closing db).f v = .var v.dummy := by
  simp [PTree.closing, Subst.ofFun, h]

theorem closing_f_of_not_mem {db : Database} {T : PTree} {v : Var} (h : v ∉ T.allVars db) :
    (T.closing db).f v = .var v := by
  simp [PTree.closing, Subst.ofFun, h]

theorem closing_typed (db : Database) (T : PTree) : (T.closing db).Typed := by
  intro v
  by_cases h : v ∈ T.allVars db
  · rw [closing_f_of_mem h]
    exact ⟨rfl, fun _ => rfl⟩
  · rw [closing_f_of_not_mem h]
    exact Ty.fits_refl _

/-- Under the closing, an expression of the tree has the dummies of its variables. -/
theorem vars_closing_apply {db : Database} {T : PTree} {e : Exp} (he : e.vars ⊆ T.allVars db) :
    ((T.closing db).apply e).vars = e.vars.image Var.dummy := by
  rw [Subst.vars_apply, ← Finset.biUnion_singleton]
  apply Finset.biUnion_congr rfl
  intro v hv
  rw [closing_f_of_mem (he hv)]
  simp [Exp.vars]

/-- And the same constants. -/
theorem consts_closing_apply {db : Database} {T : PTree} {e : Exp} (he : e.vars ⊆ T.allVars db) :
    ((T.closing db).apply e).consts = e.consts := by
  rw [Subst.consts_apply]
  ext x
  simp only [Finset.mem_union, Finset.mem_biUnion]
  constructor
  · rintro (h | ⟨v, hv, hx⟩)
    · exact h
    · rw [closing_f_of_mem (he hv)] at hx
      simp [Exp.consts] at hx
  · intro h
    exact Or.inl h

/-- A condition that holds goes on holding under the closing. -/
theorem holds_closing (db : Database) (T : PTree) (c : Consts) (k : Cond)
    (hk1 : k.1.vars ⊆ T.allVars db) (hk2 : k.2.vars ⊆ T.allVars db) (hname : k.1.ty.name = true)
    (h : k.Holds c) : (k.apply (T.closing db)).Holds c := by
  obtain ⟨n, e⟩ := k
  simp only [Cond.Holds, Cond.apply] at h ⊢
  have hvars := vars_closing_apply (db := db) (T := T) hk2
  have hconsts := consts_closing_apply (db := db) (T := T) hk2
  cases n with
  | var w =>
    have hw : w ∈ T.allVars db := hk1 (by simp [Exp.vars])
    rw [Subst.apply_var, closing_f_of_mem hw]
    intro hmem
    rw [Consts.mem_names] at hmem
    rcases hmem with ⟨v, hv, _, hvw⟩ | ⟨p, _, _, hp⟩ | ⟨p, _, m, _, hp⟩
    · rw [hvars, Finset.mem_image] at hv
      obtain ⟨u, hu, hu'⟩ := hv
      have hvw' : w.dummy = v := Exp.var.inj hvw
      subst hvw'
      have huw : u = w := Var.dummy_injective hu'
      subst huw
      apply h
      rw [Consts.mem_names]
      exact Or.inl ⟨u, hu, by simpa [Exp.ty] using hname, rfl⟩
    · simp at hp
    · simp at hp
  | const m t =>
    rw [Subst.apply_const]
    intro hmem
    apply h
    rw [Consts.mem_names] at hmem ⊢
    rw [hconsts] at hmem
    rcases hmem with ⟨v, _, _, hv⟩ | h2 | h3
    · simp at hv
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr h3)
  | app f t args =>
    simp only [Subst.apply]
    exact Consts.app_not_mem_names c f t _ _

/-- The variables of the closed tree: the dummies of the tree's variables. -/
theorem allVars_close (db : Database) (T : PTree) :
    (T.close db).allVars db = (T.allVars db).image Var.dummy := by
  ext v
  simp only [PTree.close, mem_allVars, exprs_subst, List.mem_map, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, hv⟩
    have hsub : e.vars ⊆ T.allVars db := fun w hw => (mem_allVars db T w).2 ⟨e, he, hw⟩
    rw [vars_closing_apply hsub, Finset.mem_image] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    exact ⟨u, ⟨e, he, hu⟩, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨e, he, hue⟩ := hu
    have hsub : e.vars ⊆ T.allVars db := fun w hw => (mem_allVars db T w).2 ⟨e, he, hw⟩
    refine ⟨_, ⟨e, he, rfl⟩, ?_⟩
    rw [vars_closing_apply hsub, Finset.mem_image]
    exact ⟨u, hue, rfl⟩

/-- In a valid tree of a well-formed database, the name of every condition is a name:
the first binder of a pair is bound, and the substitution is typed. -/
theorem conds_name {db : Database} (hwf : db.WF) {st : Statement} {T : PTree} (h : Shape db st T) :
    ∀ k ∈ T.conds db, k.1.ty.name = true := by
  induction h with
  | hyp e _ => simp [PTree.conds]
  | step e a θ cs A hA hθ _ _ _ ih =>
    intro k hk
    simp only [PTree.conds, List.mem_append] at hk
    rcases hk with hk | hk
    · unfold stepConds at hk
      rw [hA] at hk
      simp only [List.mem_map] at hk
      obtain ⟨p, hp, rfl⟩ := hk
      exact (hθ p.1).2 ((hwf A (List.mem_of_getElem? hA)).pairs_bound p hp)
    · rw [PTree.mem_condsList] at hk
      obtain ⟨c, hc, hk⟩ := hk
      exact ih c hc k hk

/-- Closing is a step of its own: a valid tree whose variables are of sorts that allow
dummies, with every variable made a dummy, is a proof of the statement under the
closing. -/
theorem close_isProof (db : Database) (hwf : db.WF) (st : Statement) (θ : Subst) (T : PTree)
    (hv : Valid db (st.subst θ) T) (he : T.expr = θ.apply st.concl)
    (hd : ∀ v ∈ T.allVars db, st.dummies v.ty.sort = true) :
    IsProof db (st.subst ((T.closing db).comp θ)) (T.close db) := by
  obtain ⟨hshape, hconds⟩ := hv
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [← Statement.subst_subst]
    exact hshape.subst (closing_typed db T)
  · intro k hk
    rw [PTree.close, conds_subst, List.mem_map] at hk
    obtain ⟨k', hk', rfl⟩ := hk
    obtain ⟨h1, h2⟩ := cond_mem_exprs db T k' hk'
    have hsub1 : k'.1.vars ⊆ T.allVars db := fun w hw => (mem_allVars db T w).2 ⟨_, h1, hw⟩
    have hsub2 : k'.2.vars ⊆ T.allVars db := fun w hw => (mem_allVars db T w).2 ⟨_, h2, hw⟩
    exact holds_closing db T _ k' hsub1 hsub2 (conds_name hwf hshape k' hk') (hconds k' hk')
  · rw [PTree.close, expr_subst, he, ← Subst.apply_comp]
    rfl
  · intro v hv
    rw [allVars_close, Finset.mem_image] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    exact ⟨rfl, hd u hu⟩

end Theory
