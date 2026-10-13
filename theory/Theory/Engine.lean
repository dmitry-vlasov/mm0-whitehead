/-
The engine lemmas (milestone 5 of `docs/THEORY.md`): the arguments the production
engine rests on where it does more than the reference engine, as facts about joins and
conditions.

- *Restriction* (`DESIGN.md`, change 5): a proof goes up with its substitution
  restricted to the visible variables. The join with the siblings and the node's
  unifier gives the same answers on the visible variables as the join with the full
  substitution, provided the variables dropped are mentioned by no other member of the
  join (`joinAll_restrict_exists`, `joinAll_restrict_instance`).
- *Key*: two proofs with the same restricted substitution are interchangeable above:
  the joins exist together and agree, up to instance each way, on the visible
  variables, and every condition on visible variables holds for one exactly when it
  holds for the other (`joinAll_key`, `joinAll_key_holds`).
- *Settled*: a condition whose name is a variable that a substitution does not mention
  holds under the substitution exactly when it holds as it is (`settled`); a join
  mentions only what its members mention (`joinAll_mentions`), so a name that no member
  mentions is settled by the join.

"Same up to instance each way" is what the postulate allows: a most general unifier is
unique up to renaming, and the postulate fixes no choice.
-/
import Theory.Generality

namespace Theory

open State

/-! ### What a substitution mentions -/

/-- The variables a substitution mentions: those it moves, and those in what it puts
for them. -/
def Subst.Mentions (θ : Subst) (v : Var) : Prop := v ∈ θ.dom ∨ ∃ u ∈ θ.dom, v ∈ (θ.f u).vars

theorem Subst.f_eq_of_not_mentions {θ : Subst} {v : Var} (h : ¬ θ.Mentions v) : θ.f v = .var v :=
  Subst.f_eq_of_not_mem fun hd => h (Or.inl hd)

theorem Subst.eq_of_mem_vars_f {θ : Subst} {u v : Var} (h : v ∈ (θ.f u).vars) (hv : ¬ θ.Mentions v) : v = u := by
  by_cases hu : u ∈ θ.dom
  · exact absurd (Or.inr ⟨u, hu, h⟩) hv
  · rw [Subst.f_eq_of_not_mem hu] at h
    simpa [Exp.vars] using h

/-- A variable of an image is mentioned or is the variable itself. -/
theorem Subst.mentions_of_mem_vars_f {θ : Subst} {u v : Var} (h : v ∈ (θ.f u).vars) : θ.Mentions v ∨ v = u := by
  by_cases hm : θ.Mentions v
  · exact Or.inl hm
  · exact Or.inr (Subst.eq_of_mem_vars_f h hm)

theorem Problem.mem_vars {E : Problem} {v : Var} : v ∈ E.vars ↔ ∃ p ∈ E, v ∈ p.1.vars ∨ v ∈ p.2.vars := by
  induction E with
  | nil => simp [Problem.vars]
  | cons p E ih =>
    rw [Problem.vars_cons, Finset.mem_union, Finset.mem_union, ih]
    simp only [List.mem_cons]
    constructor
    · rintro ((h | h) | ⟨q, hq, h⟩)
      · exact ⟨p, Or.inl rfl, Or.inl h⟩
      · exact ⟨p, Or.inl rfl, Or.inr h⟩
      · exact ⟨q, Or.inr hq, h⟩
    · rintro ⟨q, (rfl | hq), h⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, hq, h⟩

theorem Subst.mem_eqs {θ : Subst} {p : Exp × Exp} : p ∈ θ.eqs ↔ ∃ u ∈ θ.dom, p = (.var u, θ.f u) := by
  simp only [Subst.eqs, List.mem_map, Finset.mem_sort]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩

/-- The variables of the equational form are what the substitution mentions. -/
theorem Subst.mem_vars_eqs {θ : Subst} {v : Var} : v ∈ Problem.vars θ.eqs ↔ θ.Mentions v := by
  rw [Problem.mem_vars]
  constructor
  · rintro ⟨p, hp, h⟩
    obtain ⟨u, hu, rfl⟩ := Subst.mem_eqs.1 hp
    simp only [Exp.vars, Finset.mem_singleton] at h
    rcases h with rfl | h
    · exact Or.inl hu
    · exact Or.inr ⟨u, hu, h⟩
  · rintro (h | ⟨u, hu, h⟩)
    · exact ⟨(.var v, θ.f v), Subst.mem_eqs.2 ⟨v, h, rfl⟩, Or.inl (by simp [Exp.vars])⟩
    · exact ⟨(.var u, θ.f u), Subst.mem_eqs.2 ⟨u, hu, rfl⟩, Or.inr h⟩

/-- A unifier mentions only the variables of its problem. -/
theorem mgu_mentions (U : Unification) {E : Problem} {θ : Subst} (h : U.mgu E = some θ) {v : Var}
    (hv : θ.Mentions v) : v ∈ E.vars := by
  rcases hv with hv | ⟨u, hu, hv⟩
  · exact U.dom_sub E θ h v hv
  · rcases U.range_sub E θ h u v hv with hv | rfl
    · exact hv
    · exact U.dom_sub E θ h v hu

/-- A join mentions only what its members mention. -/
theorem joinAll_mentions (U : Unification) :
    ∀ (θs : List Subst) (θ : Subst), U.joinAll θs = some θ → ∀ v, θ.Mentions v → ∃ σ ∈ θs, σ.Mentions v
  | [], θ, h, v, hv => by
    simp only [Unification.joinAll, Option.some.injEq] at h
    subst h
    rcases hv with hv | ⟨u, hu, _⟩
    · simp [Subst.id] at hv
    · simp [Subst.id] at hu
  | σ₀ :: θs, θ, h, v, hv => by
    simp only [Unification.joinAll, Option.bind_eq_some_iff] at h
    obtain ⟨η, hη, hj⟩ := h
    have := mgu_mentions U hj hv
    rw [Problem.vars_append, Finset.mem_union, Subst.mem_vars_eqs, Subst.mem_vars_eqs] at this
    rcases this with h | h
    · exact ⟨σ₀, List.mem_cons_self, h⟩
    · obtain ⟨σ, hσ, hm⟩ := joinAll_mentions U θs η hη v h
      exact ⟨σ, List.mem_cons_of_mem _ hσ, hm⟩

/-! ### Absorption, idempotence, restriction -/

/-- `ρ` absorbs `σ` exactly when it agrees with `ρ ∘ σ` on what `σ` moves. -/
theorem Subst.comp_eq_iff {ρ σ : Subst} : ρ.comp σ = ρ ↔ ∀ v ∈ σ.dom, ρ.apply (σ.f v) = ρ.f v := by
  constructor
  · intro h v _
    exact congrArg (fun τ => τ.f v) h
  · intro h
    apply Subst.ext
    funext v
    show ρ.apply (σ.f v) = ρ.f v
    by_cases hv : v ∈ σ.dom
    · exact h v hv
    · rw [Subst.f_eq_of_not_mem hv, Subst.apply_var]

/-- A substitution that moves no variable of an expression leaves it. -/
theorem Subst.apply_eq_self {θ : Subst} {e : Exp} (h : ∀ w ∈ e.vars, w ∉ θ.dom) : θ.apply e = e := by
  rw [apply_congr_vars (σ := Subst.id) e fun w hw => by
    rw [Subst.f_eq_of_not_mem (h w hw)]; rfl]
  exact Subst.apply_id e

mutual
/-- An expression a substitution leaves has no variable it moves. -/
theorem Subst.fixes_of_apply_eq (θ : Subst) : ∀ e : Exp, θ.apply e = e → ∀ w ∈ e.vars, θ.f w = .var w
  | .var v, h, w, hw => by
    simp only [Exp.vars, Finset.mem_singleton] at hw
    subst hw
    simpa using h
  | .const _ _, _, w, hw => by simp [Exp.vars] at hw
  | .app _ _ args, h, w, hw => by
    simp only [Subst.apply, Exp.app.injEq, true_and] at h
    exact Subst.fixesList_of_applyList_eq θ args h w (by simpa [Exp.vars] using hw)
theorem Subst.fixesList_of_applyList_eq (θ : Subst) :
    ∀ es : List Exp, θ.applyList es = es → ∀ w ∈ Exp.varsList es, θ.f w = .var w
  | [], _, w, hw => by simp [Exp.varsList] at hw
  | e :: es, h, w, hw => by
    simp only [Subst.applyList, List.cons.injEq] at h
    simp only [Exp.varsList, Finset.mem_union] at hw
    rcases hw with hw | hw
    · exact Subst.fixes_of_apply_eq θ e h.1 w hw
    · exact Subst.fixesList_of_applyList_eq θ es h.2 w hw
end

/-- An idempotent substitution puts nothing it moves. -/
theorem Subst.Idem.not_mem_dom {θ : Subst} (h : θ.Idem) {u w : Var} (hw : w ∈ (θ.f u).vars) : w ∉ θ.dom := by
  have hfix : θ.apply (θ.f u) = θ.f u := congrArg (fun σ => σ.f u) h
  intro hd
  exact (θ.hdom w).1 hd (Subst.fixes_of_apply_eq θ _ hfix w hw)

theorem Subst.Idem.restrict {θ : Subst} (h : θ.Idem) (V : Finset Var) : (θ.restrict V).Idem := by
  rw [Subst.Idem, Subst.comp_eq_iff]
  intro v hv
  have hvV : v ∈ V := Subst.restrict_dom_subset θ V hv
  rw [Subst.restrict_f_of_mem hvV]
  apply Subst.apply_eq_self
  intro w hw hw'
  exact h.not_mem_dom hw (Finset.mem_filter.1 hw').1

theorem Subst.comp_restrict_eq {ρ θ : Subst} (V : Finset Var) (h : ρ.comp θ = ρ) : ρ.comp (θ.restrict V) = ρ := by
  rw [Subst.comp_eq_iff] at h ⊢
  intro v hv
  have hvV : v ∈ V := Subst.restrict_dom_subset θ V hv
  rw [Subst.restrict_f_of_mem hvV]
  exact h v (Finset.mem_filter.1 hv).1

/-- The members of a join other than `θ` mention nothing `θ` moves below `V`. -/
def ApartBelow (θ : Subst) (V : Finset Var) (η : Subst) : Prop :=
  ∀ w ∈ θ.dom, w ∉ V → ¬ η.Mentions w

/-- `ρ` extended below `V`: what `θ` moves there gets `ρ ∘ θ`. -/
def Subst.extend (ρ θ : Subst) (V : Finset Var) : Subst :=
  Subst.ofFun (ρ.dom ∪ θ.dom) (fun v => if v ∈ θ.dom ∧ v ∉ V then ρ.apply (θ.f v) else ρ.f v) (by
    intro v hv
    rw [Finset.mem_union, not_or] at hv
    simp [hv.2, Subst.f_eq_of_not_mem hv.1])

theorem Subst.extend_f_below {ρ θ : Subst} {V : Finset Var} {v : Var} (hd : v ∈ θ.dom) (hv : v ∉ V) :
    (ρ.extend θ V).f v = ρ.apply (θ.f v) := by
  show (if v ∈ θ.dom ∧ v ∉ V then ρ.apply (θ.f v) else ρ.f v) = _
  simp [hd, hv]

theorem Subst.extend_f_visible {ρ θ : Subst} {V : Finset Var} {v : Var} (h : v ∈ θ.dom → v ∈ V) :
    (ρ.extend θ V).f v = ρ.f v := by
  show (if v ∈ θ.dom ∧ v ∉ V then ρ.apply (θ.f v) else ρ.f v) = _
  rw [ite_eq_right]
  rintro ⟨hd, hv⟩
  exact hv (h hd)

theorem Subst.extend_typed {ρ θ : Subst} (hρ : ρ.Typed) (hθ : θ.Typed) (V : Finset Var) : (ρ.extend θ V).Typed := by
  intro v
  by_cases h : v ∈ θ.dom ∧ v ∉ V
  · rw [Subst.extend_f_below h.1 h.2]
    exact Subst.Typed.comp hρ hθ v
  · rw [Subst.extend_f_visible fun hd => by_contra fun hv => h ⟨hd, hv⟩]
    exact hρ v

theorem Subst.extend_apply {ρ θ : Subst} {V : Finset Var} {e : Exp} (h : ∀ w ∈ e.vars, w ∈ θ.dom → w ∈ V) :
    (ρ.extend θ V).apply e = ρ.apply e :=
  apply_congr_vars e fun w hw => Subst.extend_f_visible (h w hw)

/-- The extension absorbs `θ` when `ρ` absorbs its restriction. -/
theorem Subst.extend_comp_self {ρ θ : Subst} {V : Finset Var} (hθ : θ.Idem) (h : ρ.comp (θ.restrict V) = ρ) :
    (ρ.extend θ V).comp θ = ρ.extend θ V := by
  rw [Subst.comp_eq_iff]
  intro v hv
  rw [Subst.extend_apply fun w hw hd => absurd hd (hθ.not_mem_dom hw)]
  by_cases hvV : v ∈ V
  · rw [Subst.extend_f_visible fun _ => hvV]
    have := (Subst.comp_eq_iff.1 h) v (Finset.mem_filter.2 ⟨hv, hvV⟩)
    rwa [Subst.restrict_f_of_mem hvV] at this
  · rw [Subst.extend_f_below hv hvV]

/-- The extension absorbs a member that mentions nothing below `V`. -/
theorem Subst.extend_comp_other {ρ θ η : Subst} {V : Finset Var} (hη : ApartBelow θ V η) (h : ρ.comp η = ρ) :
    (ρ.extend θ V).comp η = ρ.extend θ V := by
  rw [Subst.comp_eq_iff] at h ⊢
  intro v hv
  have hvis : v ∈ θ.dom → v ∈ V := fun hd => by_contra fun hV => hη v hd hV (Or.inl hv)
  rw [Subst.extend_apply fun w hw hd => by_contra fun hV => hη w hd hV (Or.inr ⟨v, hv, hw⟩),
    Subst.extend_f_visible hvis]
  exact h v hv

/-! ### Joins with a restricted member -/

/-- `ρ` absorbs every member. -/
def AbsorbsAll (ρ : Subst) (θs : List Subst) : Prop := ∀ σ ∈ θs, ρ.comp σ = ρ

theorem absorbsAll_middle {ρ θ : Subst} {L₁ L₂ : List Subst} :
    AbsorbsAll ρ (L₁ ++ θ :: L₂) ↔ ρ.comp θ = ρ ∧ AbsorbsAll ρ (L₁ ++ L₂) := by
  simp only [AbsorbsAll, List.mem_append, List.mem_cons]
  constructor
  · intro h
    exact ⟨h θ (Or.inr (Or.inl rfl)), fun σ hσ => h σ (hσ.elim Or.inl (Or.inr ∘ Or.inr))⟩
  · rintro ⟨h1, h2⟩ σ (hσ | rfl | hσ)
    · exact h2 σ (Or.inl hσ)
    · exact h1
    · exact h2 σ (Or.inr hσ)

theorem AbsorbsAll.restrict {ρ θ : Subst} {L₁ L₂ : List Subst} (V : Finset Var)
    (h : AbsorbsAll ρ (L₁ ++ θ :: L₂)) : AbsorbsAll ρ (L₁ ++ θ.restrict V :: L₂) := by
  rw [absorbsAll_middle] at h ⊢
  exact ⟨Subst.comp_restrict_eq V h.1, h.2⟩

theorem AbsorbsAll.extend {ρ θ : Subst} {V : Finset Var} {L₁ L₂ : List Subst} (hθ : θ.Idem)
    (hL : ∀ η ∈ L₁ ++ L₂, ApartBelow θ V η) (h : AbsorbsAll ρ (L₁ ++ θ.restrict V :: L₂)) :
    AbsorbsAll (ρ.extend θ V) (L₁ ++ θ :: L₂) := by
  rw [absorbsAll_middle] at h ⊢
  exact ⟨Subst.extend_comp_self hθ h.1, fun η hη => Subst.extend_comp_other (hL η hη) (h.2 η hη)⟩

theorem idem_middle {θ θ' : Subst} {L₁ L₂ : List Subst} (hθ : θ'.Idem) (h : ∀ σ ∈ L₁ ++ θ :: L₂, σ.Idem) :
    ∀ σ ∈ L₁ ++ θ' :: L₂, σ.Idem := by
  intro σ hσ
  simp only [List.mem_append, List.mem_cons] at hσ h
  rcases hσ with hσ | rfl | hσ
  · exact h σ (Or.inl hσ)
  · exact hθ
  · exact h σ (Or.inr (Or.inr hσ))

/-- The join of a list is, semantically, the most general typed substitution absorbing
every member: this is `joinAll_absorbs`, `joinAll_typed`, `joinAll_idem` and
`joinAll_mostGeneral` in one place. -/
theorem joinAll_spec (U : Unification) {θs : List Subst} (hidem : ∀ σ ∈ θs, σ.Idem) :
    (∀ θ, U.joinAll θs = some θ → θ.Typed ∧ θ.Idem ∧ AbsorbsAll θ θs) ∧
    (∀ ρ, ρ.Typed → AbsorbsAll ρ θs → ∃ θ, U.joinAll θs = some θ ∧ ρ.comp θ = ρ) := by
  refine ⟨fun θ h => ⟨joinAll_typed U θs θ h, joinAll_idem U θs θ h, joinAll_absorbs U θs θ h⟩, ?_⟩
  intro ρ hρ habs
  obtain ⟨θ, hθ, hinst⟩ := joinAll_mostGeneral U θs ρ hρ hidem habs
  exact ⟨θ, hθ, Subst.comp_eq_of_instance (joinAll_idem U θs θ hθ) hinst⟩

/-- **Restriction, existence**: the join with the full member exists exactly when the
join with the restricted one does. -/
theorem joinAll_restrict_exists (U : Unification) {θ : Subst} (V : Finset Var) {L₁ L₂ : List Subst}
    (hθ : θ.Idem) (hθt : θ.Typed) (hidem : ∀ σ ∈ L₁ ++ θ :: L₂, σ.Idem) (hL : ∀ η ∈ L₁ ++ L₂, ApartBelow θ V η) :
    (∃ J, U.joinAll (L₁ ++ θ :: L₂) = some J) ↔ ∃ J', U.joinAll (L₁ ++ θ.restrict V :: L₂) = some J' := by
  constructor
  · rintro ⟨J, hJ⟩
    obtain ⟨hJt, _, hJa⟩ := (joinAll_spec U hidem).1 J hJ
    obtain ⟨J', hJ', _⟩ := (joinAll_spec U (idem_middle (hθ.restrict V) hidem)).2 J hJt (hJa.restrict V)
    exact ⟨J', hJ'⟩
  · rintro ⟨J', hJ'⟩
    obtain ⟨hJt, _, hJa⟩ := (joinAll_spec U (idem_middle (hθ.restrict V) hidem)).1 J' hJ'
    obtain ⟨J, hJ, _⟩ := (joinAll_spec U hidem).2 (J'.extend θ V) (Subst.extend_typed hJt hθt V) (hJa.extend hθ hL)
    exact ⟨J, hJ⟩

/-- **Restriction, the answers**: the join with the full member is an instance of the
join with the restricted one, and on the visible variables also the other way round. -/
theorem joinAll_restrict_instance (U : Unification) {θ : Subst} (V : Finset Var) {L₁ L₂ : List Subst}
    (hθ : θ.Idem) (hθt : θ.Typed) (hidem : ∀ σ ∈ L₁ ++ θ :: L₂, σ.Idem) (hL : ∀ η ∈ L₁ ++ L₂, ApartBelow θ V η)
    {J J' : Subst} (hJ : U.joinAll (L₁ ++ θ :: L₂) = some J) (hJ' : U.joinAll (L₁ ++ θ.restrict V :: L₂) = some J') :
    (∃ δ : Subst, δ.Typed ∧ ∀ v, J.f v = δ.apply (J'.f v)) ∧
    (∃ δ : Subst, δ.Typed ∧ ∀ v, (v ∈ θ.dom → v ∈ V) → J'.f v = δ.apply (J.f v)) := by
  have hidem' := idem_middle (hθ.restrict V) hidem
  obtain ⟨hJt, _, hJa⟩ := (joinAll_spec U hidem).1 J hJ
  obtain ⟨hJt', _, hJa'⟩ := (joinAll_spec U hidem').1 J' hJ'
  constructor
  · obtain ⟨J₀, hJ₀, habs⟩ := (joinAll_spec U hidem').2 J hJt (hJa.restrict V)
    rw [hJ'] at hJ₀
    obtain rfl := Option.some.inj hJ₀
    exact ⟨J, hJt, fun v => (congrArg (fun τ => τ.f v) habs).symm⟩
  · obtain ⟨J₀, hJ₀, habs⟩ := (joinAll_spec U hidem).2 (J'.extend θ V) (Subst.extend_typed hJt' hθt V) (hJa'.extend hθ hL)
    rw [hJ] at hJ₀
    obtain rfl := Option.some.inj hJ₀
    refine ⟨J'.extend θ V, Subst.extend_typed hJt' hθt V, fun v hv => ?_⟩
    rw [← Subst.extend_f_visible (ρ := J') hv]
    exact (congrArg (fun τ => τ.f v) habs).symm

/-- **Key**: two members with the same restriction give joins that exist together, and
the join with the first is an instance of the join with the second on the variables
visible for the second. Applied both ways, the two joins agree on the variables visible
for both. -/
theorem joinAll_key (U : Unification) {θ₁ θ₂ : Subst} (V : Finset Var) {L₁ L₂ : List Subst}
    (h₁ : θ₁.Idem) (h₁t : θ₁.Typed) (h₂ : θ₂.Idem) (h₂t : θ₂.Typed) (hidem : ∀ σ ∈ L₁ ++ L₂, σ.Idem)
    (hL₁ : ∀ η ∈ L₁ ++ L₂, ApartBelow θ₁ V η) (hL₂ : ∀ η ∈ L₁ ++ L₂, ApartBelow θ₂ V η)
    (hkey : θ₁.restrict V = θ₂.restrict V) :
    ((∃ J, U.joinAll (L₁ ++ θ₁ :: L₂) = some J) ↔ ∃ J, U.joinAll (L₁ ++ θ₂ :: L₂) = some J) ∧
    ∀ J₁ J₂, U.joinAll (L₁ ++ θ₁ :: L₂) = some J₁ → U.joinAll (L₁ ++ θ₂ :: L₂) = some J₂ →
      ∃ δ : Subst, δ.Typed ∧ ∀ v, (v ∈ θ₂.dom → v ∈ V) → J₁.f v = δ.apply (J₂.f v) := by
  have hidem₁ : ∀ σ ∈ L₁ ++ θ₁ :: L₂, σ.Idem := by
    intro σ hσ
    simp only [List.mem_append, List.mem_cons] at hσ hidem
    rcases hσ with hσ | rfl | hσ
    · exact hidem σ (Or.inl hσ)
    · exact h₁
    · exact hidem σ (Or.inr hσ)
  have hidem₂ : ∀ σ ∈ L₁ ++ θ₂ :: L₂, σ.Idem := by
    intro σ hσ
    simp only [List.mem_append, List.mem_cons] at hσ hidem
    rcases hσ with hσ | rfl | hσ
    · exact hidem σ (Or.inl hσ)
    · exact h₂
    · exact hidem σ (Or.inr hσ)
  constructor
  · rw [joinAll_restrict_exists U V h₁ h₁t hidem₁ hL₁, joinAll_restrict_exists U V h₂ h₂t hidem₂ hL₂, hkey]
  · intro J₁ J₂ hJ₁ hJ₂
    obtain ⟨J', hJ'⟩ := (joinAll_restrict_exists U V h₁ h₁t hidem₁ hL₁).1 ⟨J₁, hJ₁⟩
    obtain ⟨⟨δ₁, hδ₁, hi₁⟩, _⟩ := joinAll_restrict_instance U V h₁ h₁t hidem₁ hL₁ hJ₁ hJ'
    rw [hkey] at hJ'
    obtain ⟨_, ⟨δ₂, hδ₂, hi₂⟩⟩ := joinAll_restrict_instance U V h₂ h₂t hidem₂ hL₂ hJ₂ hJ'
    refine ⟨δ₁.comp δ₂, Subst.Typed.comp hδ₁ hδ₂, fun v hv => ?_⟩
    rw [hi₁ v, hi₂ v hv, Subst.apply_comp]

/-! ### Conditions -/

/-- A condition that holds under a substitution holds under one it is an instance of on
the condition's variables. -/
theorem holds_of_agree {c : Consts} {ρ₁ ρ₂ δ : Subst} (hδ : δ.Typed) {k : Cond}
    (h : ∀ v ∈ k.1.vars ∪ k.2.vars, ρ₁.f v = δ.apply (ρ₂.f v)) (hh : (k.apply ρ₁).Holds c) : (k.apply ρ₂).Holds c := by
  have heq : k.apply ρ₁ = k.apply (δ.comp ρ₂) := by
    simp only [Cond.apply]
    rw [apply_congr_vars (σ := δ.comp ρ₂) k.1 fun v hv => h v (Finset.mem_union_left _ hv),
      apply_congr_vars (σ := δ.comp ρ₂) k.2 fun v hv => h v (Finset.mem_union_right _ hv)]
  exact holds_of_instance hδ rfl (heq ▸ hh)

/-- **Key, the conditions**: under the two joins, a condition on the variables visible
for both holds for one exactly when it holds for the other. -/
theorem joinAll_key_holds (U : Unification) {θ₁ θ₂ : Subst} (V : Finset Var) {L₁ L₂ : List Subst}
    (h₁ : θ₁.Idem) (h₁t : θ₁.Typed) (h₂ : θ₂.Idem) (h₂t : θ₂.Typed) (hidem : ∀ σ ∈ L₁ ++ L₂, σ.Idem)
    (hL₁ : ∀ η ∈ L₁ ++ L₂, ApartBelow θ₁ V η) (hL₂ : ∀ η ∈ L₁ ++ L₂, ApartBelow θ₂ V η)
    (hkey : θ₁.restrict V = θ₂.restrict V)
    {J₁ J₂ : Subst} (hJ₁ : U.joinAll (L₁ ++ θ₁ :: L₂) = some J₁) (hJ₂ : U.joinAll (L₁ ++ θ₂ :: L₂) = some J₂)
    (c : Consts) {k : Cond} (hk : ∀ v ∈ k.1.vars ∪ k.2.vars, (v ∈ θ₁.dom → v ∈ V) ∧ (v ∈ θ₂.dom → v ∈ V)) :
    (k.apply J₁).Holds c ↔ (k.apply J₂).Holds c := by
  obtain ⟨δ, hδ, hi⟩ := (joinAll_key U V h₁ h₁t h₂ h₂t hidem hL₁ hL₂ hkey).2 J₁ J₂ hJ₁ hJ₂
  obtain ⟨δ', hδ', hi'⟩ := (joinAll_key U V h₂ h₂t h₁ h₁t hidem hL₂ hL₁ hkey.symm).2 J₂ J₁ hJ₂ hJ₁
  exact ⟨holds_of_agree hδ (fun v hv => hi v (hk v hv).2), holds_of_agree hδ' (fun v hv => hi' v (hk v hv).1)⟩

theorem Consts.var_mem_names (c : Consts) (y : Var) (e : Exp) : Exp.var y ∈ c.names e ↔ y ∈ e.vars ∧ y.ty.name = true := by
  rw [Consts.mem_names]
  constructor
  · rintro (⟨v, hv, hn, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩)
    · cases h; exact ⟨hv, hn⟩
    · cases h
    · cases h
  · rintro ⟨hv, hn⟩
    exact Or.inl ⟨y, hv, hn, rfl⟩

/-- **Settled**: a condition whose name is a variable the substitution does not mention
holds under it exactly when it holds as it is. -/
theorem settled {J : Subst} {y : Var} (hy : ¬ J.Mentions y) (e : Exp) (c : Consts) :
    Cond.Holds c (Cond.apply J (Exp.var y, e)) ↔ Cond.Holds c (Exp.var y, e) := by
  simp only [Cond.apply, Subst.apply_var, Subst.f_eq_of_not_mentions hy, Cond.Holds, Consts.var_mem_names]
  have : y ∈ (J.apply e).vars ↔ y ∈ e.vars := by
    rw [Subst.vars_apply, Finset.mem_biUnion]
    constructor
    · rintro ⟨v, hv, h⟩
      rw [Subst.eq_of_mem_vars_f h hy]
      exact hv
    · intro h
      exact ⟨y, h, by rw [Subst.f_eq_of_not_mentions hy]; simp [Exp.vars]⟩
  rw [this]

/-- A join settles every name that none of its members mentions. -/
theorem settled_joinAll (U : Unification) {θs : List Subst} {J : Subst} (hJ : U.joinAll θs = some J)
    {y : Var} (hy : ∀ σ ∈ θs, ¬ σ.Mentions y) (e : Exp) (c : Consts) :
    Cond.Holds c (Cond.apply J (Exp.var y, e)) ↔ Cond.Holds c (Exp.var y, e) :=
  settled (fun h => by obtain ⟨σ, hσ, hm⟩ := joinAll_mentions U θs J hJ y h; exact hy σ hσ hm) e c

/-! ### In the reference engine

The three lemmas for the join at an assertion node of the reference engine. The
visible variables of an expression node are those of its expression and of the
statement; what a child's entry moves below them is in the blocks of the assertion
nodes of its tree, which no other member of the join mentions. -/

/-- The variables of the statement. -/
def Statement.vars (st : Statement) : Finset Var :=
  st.concl.vars ∪ (st.hyps.map Exp.vars).foldr (· ∪ ·) ∅

theorem mem_foldr_hyps_vars (hyps : List Exp) (v : Var) :
    v ∈ (hyps.map Exp.vars).foldr (· ∪ ·) ∅ → ∃ e ∈ hyps, v ∈ e.vars := by
  induction hyps with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.foldr_cons, Finset.mem_union, List.mem_cons]
    rintro (h | h)
    · exact ⟨e, Or.inl rfl, h⟩
    · obtain ⟨e', he', hv⟩ := ih h
      exact ⟨e', Or.inr he', hv⟩

theorem Statement.vars_lt {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    {v : Var} (hv : v ∈ st.vars) : v.id < s.freshBase := by
  apply hs.fresh_gt
  rcases Finset.mem_union.1 hv with h | h
  · exact Or.inl h
  · exact Or.inr (mem_foldr_hyps_vars st.hyps v h)

theorem Statement.mem_vars_of_hyp {st : Statement} {h : ℕ} (hh : h < st.hyps.length) {v : Var}
    (hv : v ∈ st.hyps[h]!.vars) : v ∈ st.vars :=
  Finset.mem_union_right _ (mem_hyps_vars st.hyps v
    ⟨st.hyps[h]!, by rw [getElem!_pos st.hyps h hh]; exact List.getElem_mem hh, hv⟩)

/-- The variables visible above expression node `c`: those of its expression and of
the statement. -/
def visible (st : Statement) (s : State) (c : ℕ) : Finset Var := s.enodes[c]!.expr.vars ∪ st.vars

/-- The block of assertion node `j`: the variables its binders are renamed to. -/
def State.InBlock (s : State) (j : ℕ) (v : Var) : Prop := s.baseOf j ≤ v.id ∧ v.id < s.baseOf (j + 1)

theorem State.baseOf_succ (s : State) (j : ℕ) : s.baseOf (j + 1) = s.baseOf j + s.stride := by
  simp only [baseOf, Nat.succ_mul]
  omega

theorem State.baseOf_le (s : State) {j j' : ℕ} (h : j ≤ j') : s.baseOf j ≤ s.baseOf j' :=
  Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem State.inBlock_eq {s : State} {j j' : ℕ} {v : Var} (h : s.InBlock j v) (h' : s.InBlock j' v) : j = j' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := s.baseOf_le (show j + 1 ≤ j' from hlt)
    unfold State.InBlock at h h'
    omega
  · have := s.baseOf_le (show j' + 1 ≤ j from hlt)
    unfold State.InBlock at h h'
    omega

theorem State.inBlock_renamed {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    {A : Assertion} (hA : A ∈ db.asserts) {x : Var} (hx : x ∈ A.vars) (j : ℕ) :
    s.InBlock j (renamed (s.baseOf j) x) := by
  have := hs.stride_gt A hA x hx
  simp only [State.InBlock, renamed, State.baseOf_succ]
  omega

theorem State.not_inBlock_of_statement {U : Unification} {db : Database} {st : Statement} {s : State}
    (hs : StateInv U db st s) {v : Var} (hv : v ∈ st.vars) (j : ℕ) : ¬ s.InBlock j v := by
  have h1 := Statement.vars_lt hs hv
  have h2 : s.freshBase ≤ s.baseOf j := Nat.le_add_right _ _
  intro h
  unfold State.InBlock at h
  omega

/-- What an assertion node's unifier mentions: the parent's expression and the node's
block. -/
theorem anode_mentions {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hwf : db.WF) {j : ℕ} (hj : j < s.anodes.size) {v : Var} (hv : s.anodes[j]!.sub.Mentions v) :
    v ∈ s.enodes[s.anodes[j]!.parent]!.expr.vars ∨ s.InBlock j v := by
  obtain ⟨A, hA⟩ := hs.anodes j hj
  have hm := mgu_mentions U hA.is_mgu hv
  rw [Problem.vars_single, Finset.mem_union] at hm
  rcases hm with h | h
  · exact Or.inl h
  · right
    rw [hs.base_eq j hj, mem_vars_rename] at h
    obtain ⟨x, hx, rfl⟩ := h
    have hmemA := List.mem_of_getElem? hA.assertion
    exact State.inBlock_renamed hs hmemA (List.mem_toFinset.1 ((hwf A hmemA).concl_vars hx)) j

/-- The variables of a child's expression: the parent's and the node's block. -/
theorem child_expr_vars {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hwf : db.WF) {j : ℕ} (hj : j < s.anodes.size) {k : ℕ} (hk : k < s.anodes[j]!.children.length) {v : Var}
    (hv : v ∈ s.enodes[s.anodes[j]!.children[k]!]!.expr.vars) :
    v ∈ s.enodes[s.anodes[j]!.parent]!.expr.vars ∨ s.InBlock j v := by
  obtain ⟨A, hA⟩ := hs.anodes j hj
  rw [(hA.children k hk).2, Subst.vars_apply, Finset.mem_biUnion] at hv
  obtain ⟨u, hu, hvu⟩ := hv
  rcases Subst.mentions_of_mem_vars_f hvu with hm | rfl
  · exact anode_mentions hs hwf hj hm
  · right
    rw [hs.base_eq j hj, mem_vars_rename] at hu
    obtain ⟨x, hx, rfl⟩ := hu
    have hk' : k < A.hyps.length := hA.children_len ▸ hk
    have hmemA := List.mem_of_getElem? hA.assertion
    exact State.inBlock_renamed hs hmemA (List.mem_toFinset.1 ((hwf A hmemA).hyps_vars _
      (by rw [getElem!_pos A.hyps k hk']; exact List.getElem_mem hk') hx)) j

/-- What an entry mentions: the statement, its node's expression, and the blocks of the
assertion nodes of its tree. -/
theorem entry_mentions {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hwf : db.WF) :
    ∀ (fuel i : ℕ), i < s.enodes.size → ∀ E ∈ sptE U st s fuel i, ∀ v, E.sub.Mentions v →
      v ∈ st.vars ∨ v ∈ s.enodes[i]!.expr.vars ∨ ∃ j ∈ E.tree.anodes, s.InBlock j v
  | 0, _, _, E, hE => by simp [sptE] at hE
  | fuel + 1, i, hi, E, hE => by
    intro v hv
    simp only [sptE, List.mem_append, List.mem_flatMap] at hE
    rcases hE with hE | ⟨j, hj, hE⟩
    · simp only [leafEntries, List.mem_filterMap, List.mem_range, Option.map_eq_some_iff] at hE
      obtain ⟨h, hh, θ, hθ, rfl⟩ := hE
      have hm := mgu_mentions U hθ hv
      rw [Problem.vars_single, Finset.mem_union] at hm
      rcases hm with h1 | h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inl (Statement.mem_vars_of_hyp hh h1)
    · obtain ⟨hj, hp⟩ := (mem_aChildren s i j).1 hj
      simp only [anodeEntries, List.mem_filterMap] at hE
      obtain ⟨tup, htup, hmk⟩ := hE
      obtain ⟨hlen, hk⟩ := mem_tuples _ tup htup
      simp only [List.length_map] at hlen hk
      split at hmk
      · exact absurd hmk (by simp)
      · rename_i J hJ
        split at hmk
        · simp only [Option.some.injEq] at hmk
          subst hmk
          obtain ⟨σ, hσ, hm⟩ := joinAll_mentions U _ J hJ v hv
          simp only [List.mem_cons, List.mem_map] at hσ
          rcases hσ with rfl | ⟨E', hE', rfl⟩
          · rcases anode_mentions hs hwf hj hm with h1 | h1
            · rw [hp] at h1
              exact Or.inr (Or.inl h1)
            · exact Or.inr (Or.inr ⟨j, by simp [SptTree.anodes], h1⟩)
          · obtain ⟨k, hk', rfl⟩ := List.mem_iff_getElem.1 hE'
            rw [← getElem!_pos tup k hk'] at hm
            have hEk := hk k (hlen ▸ hk')
            rw [getElem!_map _ _ k (hlen ▸ hk')] at hEk
            obtain ⟨A, hA⟩ := hs.anodes j hj
            have hck := (hA.children k (hlen ▸ hk')).1
            rcases entry_mentions hs hwf fuel _ hck tup[k]! hEk v hm with h1 | h1 | ⟨j', hj', h1⟩
            · exact Or.inl h1
            · rcases child_expr_vars hs hwf hj (hlen ▸ hk') h1 with h2 | h2
              · rw [hp] at h2
                exact Or.inr (Or.inl h2)
              · exact Or.inr (Or.inr ⟨j, by simp [SptTree.anodes], h2⟩)
            · refine Or.inr (Or.inr ⟨j', ?_, h1⟩)
              simp only [SptTree.anodes, List.mem_cons]
              right
              rw [SptTree.anodesList_eq_flatMap, List.mem_flatMap]
              refine ⟨tup[k]!.tree, List.mem_map_of_mem ?_, hj'⟩
              rw [getElem!_pos tup k hk']
              exact List.getElem_mem hk'
        · exact absurd hmk (by simp)

/-- The assertion nodes of a child's tree are after the node: nodes are made in order. -/
theorem anode_lt_of_child {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    {j : ℕ} (hj : j < s.anodes.size) {k : ℕ} (hk : k < s.anodes[j]!.children.length) {T : SptTree}
    (hat : T.At s s.anodes[j]!.children[k]!) : ∀ j' ∈ T.anodes, j < j' := by
  intro j' hj'
  have hle := le_of_mem_enodes hs hat _ (parent_mem_enodes hat j' hj')
  by_contra hlt
  have := hs.parent_lt_children j' j (Nat.le_of_not_lt hlt) hj s.anodes[j]!.children[k]!
    (by rw [getElem!_pos s.anodes[j]!.children k hk]; exact List.getElem_mem hk)
  omega

/-- A variable in the block of a node of a child's tree is not in the parent's
expression, not in the node's block, and not in the statement. -/
theorem below_apart {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    {j : ℕ} (hj : j < s.anodes.size) {k : ℕ} (hk : k < s.anodes[j]!.children.length) {T : SptTree}
    (hat : T.At s s.anodes[j]!.children[k]!) {j' : ℕ} (hj' : j' ∈ T.anodes) {v : Var} (hv : s.InBlock j' v) :
    v ∉ s.enodes[s.anodes[j]!.parent]!.expr.vars ∧ ¬ s.InBlock j v ∧ v ∉ st.vars := by
  have hlt := anode_lt_of_child hs hj hk hat j' hj'
  obtain ⟨A, hA⟩ := hs.anodes j hj
  refine ⟨fun hmem => ?_, fun hb => ?_, fun hst => ?_⟩
  · have h1 := hA.parent_vars_lt v hmem
    rw [hs.base_eq j hj] at h1
    have h2 := s.baseOf_le (Nat.le_of_lt hlt)
    unfold State.InBlock at hv
    omega
  · exact Nat.ne_of_lt hlt (State.inBlock_eq hb hv)
  · exact State.not_inBlock_of_statement hs hst j' hv

/-- Trees at two distinct children of an assertion node share no expression node
(`sibling_disjoint`, for two trees given separately). -/
theorem sibling_trees_disjoint {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    {j : ℕ} (hj : j < s.anodes.size) {k k' : ℕ} (hk : k < s.anodes[j]!.children.length)
    (hk' : k' < s.anodes[j]!.children.length) {T T' : SptTree} (hT : T.At s s.anodes[j]!.children[k]!)
    (hT' : T'.At s s.anodes[j]!.children[k']!) : ∀ e, e ∈ T.enodes s → e ∈ T'.enodes s → k = k' := by
  intro e he he'
  obtain ⟨L, hL⟩ := chain_suffix hs.up_lt e _ (mem_chain_of_at hs hT e he)
  obtain ⟨L', hL'⟩ := chain_suffix hs.up_lt e _ (mem_chain_of_at hs hT' e he')
  have hu := hs.up_children j hj k hk
  have hu' := hs.up_children j hj k' hk'
  rw [chain_eq hs.up_lt hu] at hL
  rw [chain_eq hs.up_lt hu'] at hL'
  have heq := List.append_inj_right' (hL.symm.trans hL') (by simp)
  simp only [List.cons.injEq] at heq
  obtain ⟨A, hinv⟩ := hs.anodes j hj
  obtain ⟨n, _, hch⟩ := hinv.children_eq
  have hkA : k < A.hyps.length := by rw [hch] at hk; simp at hk; omega
  have hk'A : k' < A.hyps.length := by rw [hch] at hk'; simp at hk'; omega
  rw [hch, getElem!_map_range _ _ k hkA, getElem!_map_range _ _ k' hk'A] at heq
  omega

/-- A variable in the block of a node of a child's tree is mentioned neither by the
node's unifier nor by an entry of another child. -/
theorem below_not_mentioned {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hwf : db.WF) {fuel j : ℕ} (hj : j < s.anodes.size) {tup : List Entry}
    (htup : tup ∈ tuples (s.anodes[j]!.children.map fun c => sptE U st s fuel c))
    {k : ℕ} (hk : k < s.anodes[j]!.children.length) {T : SptTree} (hat : T.At s s.anodes[j]!.children[k]!)
    {j' : ℕ} (hj' : j' ∈ T.anodes) {y : Var} (hb : s.InBlock j' y) :
    ¬ s.anodes[j]!.sub.Mentions y ∧
    ∀ l, l < s.anodes[j]!.children.length → l ≠ k → ¬ tup[l]!.sub.Mentions y := by
  obtain ⟨A, hA⟩ := hs.anodes j hj
  obtain ⟨hlen, htupk⟩ := mem_tuples _ tup htup
  simp only [List.length_map] at hlen htupk
  obtain ⟨h1, h2, h3⟩ := below_apart hs hj hk hat hj' hb
  refine ⟨fun hm => ?_, fun l hl hne hm => ?_⟩
  · rcases anode_mentions hs hwf hj hm with h | h
    · exact h1 h
    · exact h2 h
  · have hEl := htupk l hl
    rw [getElem!_map _ _ l hl] at hEl
    have hcl := (hA.children l hl).1
    have hlinv := sptE_inv hs fuel _ hcl tup[l]! hEl
    rcases entry_mentions hs hwf fuel _ hcl tup[l]! hEl y hm with h | h | ⟨j'', hj'', hb'⟩
    · exact h3 h
    · rcases child_expr_vars hs hwf hj hl h with h' | h'
      · exact h1 h'
      · exact h2 h'
    · obtain rfl := State.inBlock_eq hb hb'
      exact hne (sibling_trees_disjoint hs hj hl hk hlinv.at_ hat _
        (parent_mem_enodes hlinv.at_ j' hj'') (parent_mem_enodes hat j' hj'))

/-- What a child's entry moves below the visible variables is in the block of a node of
its tree. -/
theorem entry_below {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hwf : db.WF) {fuel c : ℕ} (hc : c < s.enodes.size) {E : Entry} (hE : E ∈ sptE U st s fuel c)
    {w : Var} (hw : w ∈ E.sub.dom) (hvis : w ∉ visible st s c) : ∃ j' ∈ E.tree.anodes, s.InBlock j' w := by
  rcases entry_mentions hs hwf fuel c hc E hE w (Or.inl hw) with h | h | h
  · exact absurd (Finset.mem_union_right _ h) hvis
  · exact absurd (Finset.mem_union_left _ h) hvis
  · exact h

/-- The hypotheses of the join lemmas, for the join at an assertion node: the child's
entry is idempotent and typed, every member is idempotent, and every member other than
the child's entry is apart from what it moves below the visible variables. The other
members are the node's unifier and entries of the other children. -/
theorem spt_join_hyps {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hwf : db.WF) {fuel j : ℕ} (hj : j < s.anodes.size) {tup : List Entry}
    (htup : tup ∈ tuples (s.anodes[j]!.children.map fun c => sptE U st s fuel c))
    {k : ℕ} (hk : k < s.anodes[j]!.children.length) {E : Entry} (hE : E ∈ sptE U st s fuel s.anodes[j]!.children[k]!)
    {L₁ L₂ : List Subst}
    (hmem : ∀ η ∈ L₁ ++ L₂, η = s.anodes[j]!.sub ∨ ∃ l, l < s.anodes[j]!.children.length ∧ l ≠ k ∧ η = tup[l]!.sub) :
    E.sub.Idem ∧ E.sub.Typed ∧ (∀ σ ∈ L₁ ++ E.sub :: L₂, σ.Idem) ∧
    ∀ η ∈ L₁ ++ L₂, ApartBelow E.sub (visible st s s.anodes[j]!.children[k]!) η := by
  obtain ⟨A, hA⟩ := hs.anodes j hj
  obtain ⟨hlen, htupk⟩ := mem_tuples _ tup htup
  simp only [List.length_map] at hlen htupk
  have hck := (hA.children k hk).1
  have hEinv := sptE_inv hs fuel _ hck E hE
  have hother : ∀ σ ∈ L₁ ++ L₂, σ.Idem := by
    intro σ hσ
    rcases hmem σ hσ with rfl | ⟨l, hl, _, rfl⟩
    · exact hA.idem
    · have hEl := htupk l hl
      rw [getElem!_map _ _ l hl] at hEl
      exact (sptE_inv hs fuel _ (hA.children l hl).1 _ hEl).idem
  refine ⟨hEinv.idem, hEinv.typed, ?_, ?_⟩
  · intro σ hσ
    rw [List.mem_append, List.mem_cons] at hσ
    rcases hσ with hσ | rfl | hσ
    · exact hother σ (List.mem_append_left _ hσ)
    · exact hEinv.idem
    · exact hother σ (List.mem_append_right _ hσ)
  · intro η hη w hw hvis hm
    obtain ⟨j', hj', hb⟩ := entry_below hs hwf hck hE hw hvis
    obtain ⟨hn1, hn2⟩ := below_not_mentioned hs hwf hj htup hk hEinv.at_ hj' hb
    rcases hmem η hη with rfl | ⟨l, hl, hne, rfl⟩
    · exact hn1 hm
    · exact hn2 l hl hne hm

/-- **Restriction in the reference engine** (`DESIGN.md`, change 5): at an assertion
node, a child's entry may go up with its substitution restricted to the visible
variables of its node — those of the node's expression and of the statement — without
changing whether the join with the node's unifier and the other children's entries
exists, nor, up to instance each way, what the join gives on the visible variables. -/
theorem spt_restrict {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hwf : db.WF) {fuel j : ℕ} (hj : j < s.anodes.size) {tup : List Entry}
    (htup : tup ∈ tuples (s.anodes[j]!.children.map fun c => sptE U st s fuel c))
    {k : ℕ} (hk : k < s.anodes[j]!.children.length) {E : Entry} (hE : E ∈ sptE U st s fuel s.anodes[j]!.children[k]!)
    {L₁ L₂ : List Subst}
    (hmem : ∀ η ∈ L₁ ++ L₂, η = s.anodes[j]!.sub ∨ ∃ l, l < s.anodes[j]!.children.length ∧ l ≠ k ∧ η = tup[l]!.sub) :
    ((∃ J, U.joinAll (L₁ ++ E.sub :: L₂) = some J) ↔
      ∃ J', U.joinAll (L₁ ++ E.sub.restrict (visible st s s.anodes[j]!.children[k]!) :: L₂) = some J') ∧
    ∀ J J', U.joinAll (L₁ ++ E.sub :: L₂) = some J →
      U.joinAll (L₁ ++ E.sub.restrict (visible st s s.anodes[j]!.children[k]!) :: L₂) = some J' →
      (∃ δ : Subst, δ.Typed ∧ ∀ v, J.f v = δ.apply (J'.f v)) ∧
      (∃ δ : Subst, δ.Typed ∧ ∀ v, (v ∈ E.sub.dom → v ∈ visible st s s.anodes[j]!.children[k]!) →
        J'.f v = δ.apply (J.f v)) := by
  obtain ⟨h1, h2, h3, h4⟩ := spt_join_hyps hs hwf hj htup hk hE hmem
  exact ⟨joinAll_restrict_exists U _ h1 h2 h3 h4, fun J J' hJ hJ' => joinAll_restrict_instance U _ h1 h2 h3 h4 hJ hJ'⟩

/-- **Key in the reference engine**: two entries of a child with the same substitution
on the visible variables are interchangeable in the join at the node: it exists for one
exactly when for the other, the two answers are instances of each other on the visible
variables, and a condition on visible variables holds under one exactly when under the
other. -/
theorem spt_key {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hwf : db.WF) {fuel j : ℕ} (hj : j < s.anodes.size) {tup : List Entry}
    (htup : tup ∈ tuples (s.anodes[j]!.children.map fun c => sptE U st s fuel c))
    {k : ℕ} (hk : k < s.anodes[j]!.children.length) {E E' : Entry}
    (hE : E ∈ sptE U st s fuel s.anodes[j]!.children[k]!) (hE' : E' ∈ sptE U st s fuel s.anodes[j]!.children[k]!)
    (hkey : E.sub.restrict (visible st s s.anodes[j]!.children[k]!) = E'.sub.restrict (visible st s s.anodes[j]!.children[k]!))
    {L₁ L₂ : List Subst}
    (hmem : ∀ η ∈ L₁ ++ L₂, η = s.anodes[j]!.sub ∨ ∃ l, l < s.anodes[j]!.children.length ∧ l ≠ k ∧ η = tup[l]!.sub) :
    ((∃ J, U.joinAll (L₁ ++ E.sub :: L₂) = some J) ↔ ∃ J, U.joinAll (L₁ ++ E'.sub :: L₂) = some J) ∧
    ∀ J J', U.joinAll (L₁ ++ E.sub :: L₂) = some J → U.joinAll (L₁ ++ E'.sub :: L₂) = some J' →
      (∃ δ : Subst, δ.Typed ∧ ∀ v, (v ∈ E'.sub.dom → v ∈ visible st s s.anodes[j]!.children[k]!) →
        J.f v = δ.apply (J'.f v)) ∧
      ∀ (c : Consts) (q : Cond), (∀ v ∈ q.1.vars ∪ q.2.vars,
          (v ∈ E.sub.dom → v ∈ visible st s s.anodes[j]!.children[k]!) ∧
          (v ∈ E'.sub.dom → v ∈ visible st s s.anodes[j]!.children[k]!)) →
        (Cond.Holds c (q.apply J) ↔ Cond.Holds c (q.apply J')) := by
  obtain ⟨h1, h2, h3, h4⟩ := spt_join_hyps hs hwf hj htup hk hE hmem
  obtain ⟨h1', h2', _, h4'⟩ := spt_join_hyps hs hwf hj htup hk hE' hmem
  have hidem : ∀ σ ∈ L₁ ++ L₂, σ.Idem := by
    intro σ hσ
    rw [List.mem_append] at hσ
    rcases hσ with hσ | hσ
    · exact h3 σ (List.mem_append_left _ hσ)
    · exact h3 σ (List.mem_append_right _ (List.mem_cons_of_mem _ hσ))
  exact ⟨(joinAll_key U _ h1 h2 h1' h2' hidem h4 h4' hkey).1, fun J J' hJ hJ' =>
    ⟨(joinAll_key U _ h1 h2 h1' h2' hidem h4 h4' hkey).2 J J' hJ hJ',
     fun c q hq => joinAll_key_holds U _ h1 h2 h1' h2' hidem h4 h4' hkey hJ hJ' c hq⟩⟩

/-- **Settled in the reference engine**: a condition of a child's entry whose name is
a variable in the block of a node of the entry's tree that the entry does not mention
— one that will become a dummy of its own — holds under the join at the node exactly
when it holds already, and the join does not mention the variable either: the condition
is settled for good. -/
theorem spt_settled {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hwf : db.WF) {fuel j : ℕ} (hj : j < s.anodes.size) {tup : List Entry}
    (htup : tup ∈ tuples (s.anodes[j]!.children.map fun c => sptE U st s fuel c))
    {k : ℕ} (hk : k < s.anodes[j]!.children.length) {E : Entry} (hE : E ∈ sptE U st s fuel s.anodes[j]!.children[k]!)
    {y : Var} (hy : ¬ E.sub.Mentions y) {j' : ℕ} (hj' : j' ∈ E.tree.anodes) (hb : s.InBlock j' y)
    {L₁ L₂ : List Subst}
    (hmem : ∀ η ∈ L₁ ++ L₂, η = s.anodes[j]!.sub ∨ ∃ l, l < s.anodes[j]!.children.length ∧ l ≠ k ∧ η = tup[l]!.sub)
    {J : Subst} (hJ : U.joinAll (L₁ ++ E.sub :: L₂) = some J) (e : Exp) (c : Consts) :
    (Cond.Holds c (Cond.apply J (Exp.var y, e)) ↔ Cond.Holds c (Exp.var y, e)) ∧ ¬ J.Mentions y := by
  obtain ⟨A, hA⟩ := hs.anodes j hj
  have hEinv := sptE_inv hs fuel _ (hA.children k hk).1 E hE
  obtain ⟨hn1, hn2⟩ := below_not_mentioned hs hwf hj htup hk hEinv.at_ hj' hb
  have hnot : ∀ σ ∈ L₁ ++ E.sub :: L₂, ¬ σ.Mentions y := by
    intro σ hσ
    rw [List.mem_append, List.mem_cons] at hσ
    have hother : ∀ σ ∈ L₁ ++ L₂, ¬ σ.Mentions y := fun σ hσ => by
      rcases hmem σ hσ with rfl | ⟨l, hl, hne, rfl⟩
      · exact hn1
      · exact hn2 l hl hne
    rcases hσ with hσ | rfl | hσ
    · exact hother σ (List.mem_append_left _ hσ)
    · exact hy
    · exact hother σ (List.mem_append_right _ hσ)
  exact ⟨settled_joinAll U hJ hnot e c, fun hm => by
    obtain ⟨σ, hσ, hm'⟩ := joinAll_mentions U _ J hJ y hm
    exact hnot σ hσ hm'⟩

end Theory
