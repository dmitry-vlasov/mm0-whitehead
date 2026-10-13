/-
Lemmas for generality and completeness: an instance of an idempotent substitution
absorbs it; the join of a list is most general among what absorbs every member; a
typed substitution keeps the occurrence of a name, so a condition that holds under an
instance holds under the answer; and substituting the proof of a tree is the proof
under the composed answer.
-/
import Theory.Preserve

namespace Theory

open State

/-- An instance of an idempotent substitution absorbs it. -/
theorem Subst.comp_eq_of_instance {σ θ : Subst} (hθ : θ.Idem) (h : σ.IsInstance θ) : σ.comp θ = σ := by
  obtain ⟨δ, rfl⟩ := h
  rw [Subst.comp_assoc, hθ]

/-- The join of a list of idempotent substitutions is most general among the typed
substitutions that absorb every member, and exists for them. -/
theorem joinAll_mostGeneral (U : Unification) :
    ∀ (θs : List Subst) (ρ : Subst), ρ.Typed → (∀ σ ∈ θs, σ.Idem) → (∀ σ ∈ θs, ρ.comp σ = ρ) →
      ∃ θ, U.joinAll θs = some θ ∧ ρ.IsInstance θ
  | [], ρ, _, _, _ => ⟨Subst.id, rfl, ⟨ρ, (Subst.comp_id ρ).symm⟩⟩
  | σ₀ :: θs, ρ, hρ, hidem, habs => by
    obtain ⟨η, hη, hinst⟩ := joinAll_mostGeneral U θs ρ hρ
      (fun σ hσ => hidem σ (List.mem_cons_of_mem _ hσ)) (fun σ hσ => habs σ (List.mem_cons_of_mem _ hσ))
    have hρη : ρ.comp η = ρ := Subst.comp_eq_of_instance (joinAll_idem U θs η hη) hinst
    have hsolves : Solves ρ (σ₀.eqs ++ η.eqs) := by
      intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact (Subst.solves_eqs_iff ρ σ₀).2 (habs σ₀ List.mem_cons_self) p hp
      · exact (Subst.solves_eqs_iff ρ η).2 hρη p hp
    obtain ⟨θ, hθ, hρθ⟩ := U.mostGeneral _ ρ hρ hsolves
    refine ⟨θ, ?_, hρθ⟩
    simp only [Unification.joinAll, hη, Option.bind, Unification.join]
    exact hθ

/-- A typed substitution keeps the occurrence of a name. -/
theorem mem_names_apply {δ : Subst} (hδ : δ.Typed) (c : Consts) {x e : Exp} (h : x ∈ c.names e) :
    δ.apply x ∈ c.names (δ.apply e) := by
  rw [Consts.mem_names] at h ⊢
  rcases h with ⟨v, hv, hn, rfl⟩ | ⟨p, hp, hn, rfl⟩ | ⟨p, hp, m, hm, rfl⟩
  · rw [Subst.apply_var]
    have hvars : (δ.f v).vars ⊆ (δ.apply e).vars := by
      rw [Subst.vars_apply]
      exact Finset.subset_biUnion_of_mem (fun v => (δ.f v).vars) hv
    have hconsts : (δ.f v).consts ⊆ (δ.apply e).consts := by
      rw [Subst.consts_apply]
      exact subset_trans (Finset.subset_biUnion_of_mem (fun v => (δ.f v).consts) hv) Finset.subset_union_right
    have hname : (δ.f v).ty.name = true := (hδ v).1.2 hn
    have hisname := (hδ v).2 hn
    cases hfv : δ.f v with
    | var w =>
      rw [hfv] at hvars hname
      exact Or.inl ⟨w, hvars (by simp [Exp.vars]), by simpa [Exp.ty] using hname, rfl⟩
    | const k t =>
      rw [hfv] at hconsts hname
      exact Or.inr (Or.inl ⟨(k, t), hconsts (by simp [Exp.consts]), by simpa [Exp.ty] using hname, rfl⟩)
    | app f t args =>
      rw [hfv] at hisname
      exact hisname.elim
  · rw [Subst.apply_const]
    refine Or.inr (Or.inl ⟨p, ?_, hn, rfl⟩)
    rw [Subst.consts_apply]
    exact Finset.mem_union_left _ hp
  · rw [Subst.apply_const]
    refine Or.inr (Or.inr ⟨p, ?_, m, hm, rfl⟩)
    rw [Subst.consts_apply]
    exact Finset.mem_union_left _ hp

/-- A condition that holds under an instance of an answer holds under the answer. -/
theorem holds_of_instance {c : Consts} {k : Cond} {ρ θ δ : Subst} (hδ : δ.Typed) (hρ : ρ = δ.comp θ)
    (h : (k.apply ρ).Holds c) : (k.apply θ).Holds c := by
  unfold Cond.Holds at h ⊢
  intro hmem
  apply h
  simp only [Cond.apply] at hmem ⊢
  rw [hρ, Subst.apply_comp, Subst.apply_comp]
  exact mem_names_apply hδ c hmem

/-- The step substitution under a further substitution, kept on the binders. -/
theorem stepSub_comp {db : Database} {a : ANode} {A : Assertion}
    (hA : db.asserts[a.assertion]! = A) (θ δ : Subst) :
    (δ.comp (stepSub db a θ)).restrict (PTree.binders db a.assertion) = stepSub db a (δ.comp θ) := by
  apply Subst.ext
  funext x
  show (if x ∈ PTree.binders db a.assertion then δ.apply ((stepSub db a θ).f x) else .var x) =
    (stepSub db a (δ.comp θ)).f x
  simp only [PTree.binders, hA, stepSub, Subst.ofFun, List.mem_toFinset]
  by_cases hx : x ∈ A.vars
  · simp [hx, Subst.apply_comp]
  · simp [hx]

/-- Substituting the proof of a tree is the proof under the composed answer. -/
theorem proofOf_subst {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (θ δ : Subst) : ∀ {i : ℕ} {T : SptTree}, T.At s i →
      (proofOf db s θ T).subst db δ = proofOf db s (δ.comp θ) T := by
  intro i T hat
  induction hat with
  | leaf i h => simp [proofOf, PTree.subst, Subst.apply_comp]
  | node i j cs hj hp hlen hcs ih =>
    obtain ⟨A, hinv⟩ := hs.anodes j hj
    have hA! := getElem!_of_getElem? hinv.assertion
    simp only [proofOf, PTree.subst, Subst.apply_comp]
    rw [stepSub_comp hA!]
    congr 1
    rw [PTree.substList_eq_map, proofsOf_eq_map, proofsOf_eq_map, List.map_map]
    apply List.map_congr_left
    intro t ht
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 ht
    rw [← getElem!_pos cs k hk]
    exact ih k hk

end Theory
