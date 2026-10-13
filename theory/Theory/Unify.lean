/-
A unifier for the first-order terms of MM0, and its proof of the postulate
(`Unification`): the classical algorithm (Robinson; Martelli–Montanari) on a list of
equations, substituting eagerly into the equations left, by well-founded recursion on
the variables of the problem and then its size — a binding removes a variable, the
other steps shrink the problem.

The typing of substitutions (`Ty.fits`) is the one of the production unifier: of two
variables the more general is bound to the more special (`ruUnifyStepVar`; `DESIGN.md`,
change 2); a variable is bound to a term only if the term's type fits it, and a name
variable only to a name.
-/
import Mathlib.Data.Finset.Card
import Theory.Unification

namespace Theory

/-! ### Measures -/

/-- The size of a problem. -/
def Problem.size (E : Problem) : ℕ := E.foldr (fun p n => p.1.size + p.2.size + n) 0

theorem Problem.size_cons (p : Exp × Exp) (E : Problem) :
    Problem.size (p :: E) = p.1.size + p.2.size + Problem.size E := rfl

theorem Problem.size_append (E E' : Problem) : Problem.size (E ++ E') = Problem.size E + Problem.size E' := by
  induction E with
  | nil => simp [Problem.size]
  | cons p E ih => simp only [List.cons_append, Problem.size_cons, ih]; omega

mutual
theorem Exp.size_pos : ∀ e : Exp, 0 < e.size
  | .var _ => by simp [Exp.size]
  | .const _ _ => by simp [Exp.size]
  | .app _ _ _ => by simp [Exp.size]
theorem Exp.sizeList_nonneg : ∀ es : List Exp, 0 ≤ Exp.sizeList es
  | _ => Nat.zero_le _
end

theorem Problem.vars_zip_subset : ∀ (as bs : List Exp),
    Problem.vars (as.zip bs) ⊆ Exp.varsList as ∪ Exp.varsList bs
  | [], _ => by simp [Problem.vars]
  | _ :: _, [] => by simp [Problem.vars]
  | a :: as, b :: bs => by
    simp only [List.zip_cons_cons, Problem.vars_cons, Exp.varsList]
    have := Problem.vars_zip_subset as bs
    intro v hv
    simp only [Finset.mem_union] at hv ⊢
    rcases hv with (hv | hv) | hv
    · exact Or.inl (Or.inl hv)
    · exact Or.inr (Or.inl hv)
    · rcases Finset.mem_union.1 (this hv) with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)

theorem Problem.size_zip_le : ∀ (as bs : List Exp),
    Problem.size (as.zip bs) ≤ Exp.sizeList as + Exp.sizeList bs
  | [], _ => by simp [Problem.size]
  | _ :: _, [] => by simp [Problem.size]
  | a :: as, b :: bs => by
    simp only [List.zip_cons_cons, Problem.size_cons, Exp.sizeList]
    have := Problem.size_zip_le as bs
    omega

/-! ### The algorithm -/

namespace Unify

/-- Binds `v` to `e` on top of `θ`: `θ` followed by the binding. -/
def bind (v : Var) (e : Exp) (θ : Subst) : Subst :=
  (Subst.single v e).comp θ

/-- Binds `v` to `e` in the remaining equations. -/
def bindIn (v : Var) (e : Exp) (E : Problem) : Problem :=
  E.map fun p => ((Subst.single v e).apply p.1, (Subst.single v e).apply p.2)

theorem single_f (v : Var) (e : Exp) (w : Var) : (Subst.single v e).f w = if w = v then e else .var w := rfl

theorem vars_single_apply (v : Var) (e : Exp) (q : Exp) :
    ((Subst.single v e).apply q).vars ⊆ (q.vars \ {v}) ∪ e.vars := by
  rw [Subst.vars_apply]
  intro w hw
  rw [Finset.mem_biUnion] at hw
  obtain ⟨u, hu, hwu⟩ := hw
  rw [single_f] at hwu
  split_ifs at hwu with huv
  · exact Finset.mem_union_right _ hwu
  · simp only [Exp.vars, Finset.mem_singleton] at hwu
    subst hwu
    exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hu, by simpa using huv⟩)

theorem vars_bindIn_subset (v : Var) (e : Exp) (E : Problem) :
    Problem.vars (bindIn v e E) ⊆ (Problem.vars E \ {v}) ∪ e.vars := by
  induction E with
  | nil => simp [bindIn, Problem.vars]
  | cons p E ih =>
    simp only [bindIn, List.map_cons, Problem.vars_cons] at ih ⊢
    intro w hw
    simp only [Finset.mem_union] at hw
    have h1 := vars_single_apply v e p.1
    have h2 := vars_single_apply v e p.2
    rcases hw with (hw | hw) | hw
    · rcases Finset.mem_union.1 (h1 hw) with h | h
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨by simp [(Finset.mem_sdiff.1 h).1], (Finset.mem_sdiff.1 h).2⟩)
      · exact Finset.mem_union_right _ h
    · rcases Finset.mem_union.1 (h2 hw) with h | h
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨by simp [(Finset.mem_sdiff.1 h).1], (Finset.mem_sdiff.1 h).2⟩)
      · exact Finset.mem_union_right _ h
    · rcases Finset.mem_union.1 (ih hw) with h | h
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨by simp [(Finset.mem_sdiff.1 h).1], (Finset.mem_sdiff.1 h).2⟩)
      · exact Finset.mem_union_right _ h

/-- The measure: the variables, then the size. -/
def measure (E : Problem) : ℕ × ℕ := (E.vars.card, E.size)

theorem lex_of_lt {a a' b b' : ℕ} (h : a < a') : Prod.Lex (· < ·) (· < ·) (a, b) (a', b') := Prod.Lex.left _ _ h

theorem lex_of_le_lt {a a' b b' : ℕ} (h : a ≤ a') (h' : b < b') : Prod.Lex (· < ·) (· < ·) (a, b) (a', b') := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ h'

/-- A binding removes the variable from the problem. -/
theorem measure_bind {v : Var} {e : Exp} {s t : Exp} {E : Problem} (hv : v ∈ Problem.vars ((s, t) :: E))
    (hve : v ∉ e.vars) (he : e.vars ⊆ Problem.vars ((s, t) :: E)) :
    Prod.Lex (· < ·) (· < ·) (measure (bindIn v e E)) (measure ((s, t) :: E)) := by
  apply lex_of_lt
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨v, hv, fun h => by
      rcases Finset.mem_union.1 (vars_bindIn_subset v e E h) with h | h
      · exact (Finset.mem_sdiff.1 h).2 (Finset.mem_singleton_self v)
      · exact hve h⟩
  · intro w hw
    rcases Finset.mem_union.1 (vars_bindIn_subset v e E hw) with h | h
    · rw [Problem.vars_cons]; exact Finset.mem_union_right _ (Finset.mem_sdiff.1 h).1
    · exact he h

theorem measure_drop (p : Exp × Exp) (E : Problem) :
    Prod.Lex (· < ·) (· < ·) (measure E) (measure (p :: E)) := by
  apply lex_of_le_lt
  · apply Finset.card_le_card
    rw [Problem.vars_cons]
    exact Finset.subset_union_right
  · rw [Problem.size_cons]
    have := Exp.size_pos p.1
    omega

theorem measure_zip (f f' : ℕ) (t t' : Ty) (args args' : List Exp) (E : Problem) :
    Prod.Lex (· < ·) (· < ·) (measure (args.zip args' ++ E)) (measure ((.app f t args, .app f' t' args') :: E)) := by
  apply lex_of_le_lt
  · apply Finset.card_le_card
    rw [Problem.vars_append, Problem.vars_cons]
    intro w hw
    rcases Finset.mem_union.1 hw with h | h
    · rcases Finset.mem_union.1 (Problem.vars_zip_subset args args' h) with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simpa [Exp.vars] using h))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simpa [Exp.vars] using h))
    · exact Finset.mem_union_right _ h
  · rw [Problem.size_append, Problem.size_cons]
    simp only [Exp.size]
    have := Problem.size_zip_le args args'
    omega

/-- The algorithm, on equations whose sides are already under the substitution so far.
Of two variables that fit each other, the one with the larger id is bound — the
fresher one, so that the statement's variables and the metavariables are kept, as the
production engine keeps the goal's variables over a rule's (`unifyStepVar`): the
reference state is then the production engine's tree up to the renaming of fresh
variables, which the node-by-node differential test (`diff-test --nodes`) needs. -/
def go : Problem → Subst → Option Subst
  | [], θ => some θ
  | (s, t) :: E, θ =>
    match s, t with
    | .var v, .var w =>
      if v = w then go E θ
      else if v.ty.fits w.ty ∧ (w.id < v.id ∨ ¬ w.ty.fits v.ty) then go (bindIn v (.var w) E) (bind v (.var w) θ)
      else if w.ty.fits v.ty then go (bindIn w (.var v) E) (bind w (.var v) θ)
      else none
    | .var v, .const k t =>
      if v.ty.fits t then go (bindIn v (.const k t) E) (bind v (.const k t) θ) else none
    | .const k t, .var v =>
      if v.ty.fits t then go (bindIn v (.const k t) E) (bind v (.const k t) θ) else none
    | .var v, .app f t args =>
      if v.ty.fits t ∧ v ∉ (Exp.app f t args).vars ∧ v.ty.name = false then
        go (bindIn v (.app f t args) E) (bind v (.app f t args) θ)
      else none
    | .app f t args, .var v =>
      if v.ty.fits t ∧ v ∉ (Exp.app f t args).vars ∧ v.ty.name = false then
        go (bindIn v (.app f t args) E) (bind v (.app f t args) θ)
      else none
    | .const k t, .const k' t' => if k = k' ∧ t = t' then go E θ else none
    | .app f t args, .app f' t' args' =>
      if f = f' ∧ t = t' ∧ args.length = args'.length then go (args.zip args' ++ E) θ else none
    | _, _ => none
termination_by E _ => measure E
decreasing_by
  all_goals first
    | exact measure_drop _ _
    | exact measure_zip _ _ _ _ _ _ _
    | (refine measure_bind ?_ ?_ ?_
       · simp [Problem.vars_cons, Exp.vars]
       · intro hx; simp_all [Exp.vars]
       · intro x hx; simp_all [Problem.vars_cons, Exp.vars])

/-- The most general unifier of a problem, if there is one. -/
def mgu (E : Problem) : Option Subst := go E Subst.id

/-! ### Lemmas on substitutions -/

mutual
/-- A substitution that moves no variable of an expression leaves it. -/
theorem apply_eq_self_of_apart (θ : Subst) : ∀ e : Exp, (∀ w ∈ e.vars, w ∉ θ.dom) → θ.apply e = e
  | .var v, h => by
    simp only [Subst.apply_var]
    exact Subst.f_eq_of_not_mem (h v (by simp [Exp.vars]))
  | .const _ _, _ => by simp [Subst.apply]
  | .app _ _ args, h => by
    simp only [Subst.apply]
    congr 1
    exact applyList_eq_self_of_apart θ args (by simpa [Exp.vars] using h)
theorem applyList_eq_self_of_apart (θ : Subst) :
    ∀ es : List Exp, (∀ w ∈ Exp.varsList es, w ∉ θ.dom) → θ.applyList es = es
  | [], _ => rfl
  | e :: es, h => by
    simp only [Subst.applyList]
    rw [apply_eq_self_of_apart θ e (fun w hw => h w (by simp [Exp.varsList, hw])),
      applyList_eq_self_of_apart θ es (fun w hw => h w (by simp [Exp.varsList, hw]))]
end

/-- Absorbing the binding of one variable. -/
theorem comp_single_eq {θ' : Subst} {v : Var} {e : Exp} (h : θ'.f v = θ'.apply e) :
    θ'.comp (Subst.single v e) = θ' := by
  apply Subst.ext
  funext u
  show θ'.apply ((Subst.single v e).f u) = θ'.f u
  rw [single_f]
  split_ifs with huv
  · subst huv; exact h.symm
  · exact Subst.apply_var _ _

/-- A substitution whose images avoid its domain is idempotent. -/
theorem idem_of_sep {θ : Subst} (h : ∀ u ∈ θ.dom, ∀ w ∈ (θ.f u).vars, w ∉ θ.dom) : θ.Idem := by
  apply Subst.ext
  funext u
  show θ.apply (θ.f u) = θ.f u
  by_cases hu : u ∈ θ.dom
  · exact apply_eq_self_of_apart θ _ (h u hu)
  · rw [Subst.f_eq_of_not_mem hu, Subst.apply_var, Subst.f_eq_of_not_mem hu]

theorem comp_dom_subset (θ η : Subst) : (θ.comp η).dom ⊆ θ.dom ∪ η.dom := by
  intro v hv
  simp only [Subst.comp, Finset.mem_filter] at hv
  exact hv.1

theorem single_dom_subset (v : Var) (e : Exp) : (Subst.single v e).dom ⊆ {v} := by
  intro w hw
  simp only [Subst.single] at hw
  split_ifs at hw with h
  · simp at hw
  · exact hw

theorem single_typed {v : Var} {e : Exp} (hfit : v.ty.fits e.ty) (hname : v.ty.name = true → e.IsName) :
    (Subst.single v e).Typed := by
  intro w
  rw [single_f]
  split_ifs with h
  · subst h
    exact ⟨hfit, hname⟩
  · exact ⟨Ty.fits_refl _, fun _ => trivial⟩

theorem single_eqs {v : Var} {e : Exp} (h : e ≠ .var v) : (Subst.single v e).eqs = [(.var v, e)] := by
  have hdom : (Subst.single v e).dom = {v} := by simp [Subst.single, h]
  simp only [Subst.eqs, hdom, Finset.sort_singleton, List.map_cons, List.map_nil, single_f, ↓reduceIte]

theorem apply_single_apply {θ' : Subst} {v : Var} {e : Exp} (h : θ'.comp (Subst.single v e) = θ') (q : Exp) :
    θ'.apply ((Subst.single v e).apply q) = θ'.apply q := by
  rw [← Subst.apply_comp, h]

theorem solves_cons (ρ : Subst) (p : Exp × Exp) (E : Problem) :
    Solves ρ (p :: E) ↔ ρ.apply p.1 = ρ.apply p.2 ∧ Solves ρ E := by
  simp only [Solves, List.mem_cons]
  constructor
  · intro h
    exact ⟨h p (Or.inl rfl), fun q hq => h q (Or.inr hq)⟩
  · rintro ⟨h1, h2⟩ q (rfl | hq)
    · exact h1
    · exact h2 q hq

theorem solves_append (ρ : Subst) (E E' : Problem) : Solves ρ (E ++ E') ↔ Solves ρ E ∧ Solves ρ E' := by
  simp only [Solves, List.mem_append]
  constructor
  · intro h
    exact ⟨fun q hq => h q (Or.inl hq), fun q hq => h q (Or.inr hq)⟩
  · rintro ⟨h1, h2⟩ q (hq | hq)
    · exact h1 q hq
    · exact h2 q hq

theorem length_applyList (ρ : Subst) : ∀ es : List Exp, (ρ.applyList es).length = es.length
  | [] => rfl
  | e :: es => by simp [Subst.applyList, length_applyList ρ es]

theorem applyList_eq_of_solves_zip (ρ : Subst) : ∀ (as bs : List Exp), as.length = bs.length →
    Solves ρ (as.zip bs) → ρ.applyList as = ρ.applyList bs
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: as, b :: bs, h, hs => by
    simp only [List.zip_cons_cons] at hs
    rw [solves_cons] at hs
    simp only [Subst.applyList]
    rw [hs.1, applyList_eq_of_solves_zip ρ as bs (by simpa using h) hs.2]

theorem solves_zip_of_applyList_eq (ρ : Subst) : ∀ (as bs : List Exp), as.length = bs.length →
    ρ.applyList as = ρ.applyList bs → Solves ρ (as.zip bs)
  | [], [], _, _ => fun p hp => by simp at hp
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: as, b :: bs, h, he => by
    simp only [List.zip_cons_cons]
    simp only [Subst.applyList, List.cons.injEq] at he
    rw [solves_cons]
    exact ⟨he.1, solves_zip_of_applyList_eq ρ as bs (by simpa using h) he.2⟩

mutual
/-- A variable of an expression is no larger than it under any substitution. -/
theorem size_le_of_mem_vars (ρ : Subst) : ∀ (e : Exp) (v : Var), v ∈ e.vars → (ρ.f v).size ≤ (ρ.apply e).size
  | .var w, v, h => by
    simp only [Exp.vars, Finset.mem_singleton] at h
    subst h
    simp [Subst.apply]
  | .const _ _, v, h => by simp [Exp.vars] at h
  | .app _ _ args, v, h => by
    simp only [Subst.apply, Exp.size]
    have := sizeList_le_of_mem_varsList ρ args v (by simpa [Exp.vars] using h)
    omega
theorem sizeList_le_of_mem_varsList (ρ : Subst) :
    ∀ (es : List Exp) (v : Var), v ∈ Exp.varsList es → (ρ.f v).size ≤ Exp.sizeList (ρ.applyList es)
  | [], v, h => by simp [Exp.varsList] at h
  | e :: es, v, h => by
    simp only [Exp.varsList, Finset.mem_union] at h
    simp only [Subst.applyList, Exp.sizeList]
    rcases h with h | h
    · have := size_le_of_mem_vars ρ e v h; omega
    · have := sizeList_le_of_mem_varsList ρ es v h; omega
end

theorem size_lt_of_mem_vars_app (ρ : Subst) (f : ℕ) (t : Ty) (args : List Exp) (v : Var)
    (h : v ∈ (Exp.app f t args).vars) : (ρ.f v).size < (ρ.apply (.app f t args)).size := by
  simp only [Subst.apply, Exp.size]
  have := sizeList_le_of_mem_varsList ρ args v (by simpa [Exp.vars] using h)
  omega

/-! ### The invariant of the algorithm -/

/-- The accumulated substitution: typed; its images avoid its domain; its domain is
apart from the equations; everything within the variables `V` of the original problem. -/
structure Inv (V : Finset Var) (E : Problem) (θ : Subst) : Prop where
  typed : θ.Typed
  sep : ∀ u ∈ θ.dom, ∀ w ∈ (θ.f u).vars, w ∉ θ.dom
  apart : ∀ u ∈ θ.dom, u ∉ E.vars
  evars : E.vars ⊆ V
  dom_sub : θ.dom ⊆ V
  range_sub : ∀ u, ∀ w ∈ (θ.f u).vars, w ∈ V ∨ w = u

theorem Inv.init (E : Problem) : Inv E.vars E Subst.id where
  typed := Subst.Typed.id
  sep := fun u hu => by simp [Subst.id] at hu
  apart := fun u hu => by simp [Subst.id] at hu
  evars := subset_refl _
  dom_sub := fun u hu => by simp [Subst.id] at hu
  range_sub := fun u w hw => by
    simp only [Subst.id, Exp.vars, Finset.mem_singleton] at hw
    exact Or.inr hw

theorem Inv.sub {V : Finset Var} {E E' : Problem} {θ : Subst} (h : Inv V E θ) (hsub : E'.vars ⊆ E.vars) :
    Inv V E' θ where
  typed := h.typed
  sep := h.sep
  apart := fun u hu hmem => h.apart u hu (hsub hmem)
  evars := subset_trans hsub h.evars
  dom_sub := h.dom_sub
  range_sub := h.range_sub

theorem Inv.drop {V : Finset Var} {p : Exp × Exp} {E : Problem} {θ : Subst} (h : Inv V (p :: E) θ) : Inv V E θ :=
  h.sub (by rw [Problem.vars_cons]; exact Finset.subset_union_right)

theorem Inv.zip {V : Finset Var} {f f' : ℕ} {t t' : Ty} {args args' : List Exp} {E : Problem} {θ : Subst}
    (h : Inv V ((.app f t args, .app f' t' args') :: E) θ) : Inv V (args.zip args' ++ E) θ := by
  refine h.sub ?_
  rw [Problem.vars_append, Problem.vars_cons]
  intro w hw
  rcases Finset.mem_union.1 hw with hw | hw
  · rcases Finset.mem_union.1 (Problem.vars_zip_subset args args' hw) with hw | hw
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simpa [Exp.vars] using hw))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simpa [Exp.vars] using hw))
  · exact Finset.mem_union_right _ hw

/-- A binding keeps the invariant. -/
theorem Inv.bind {V : Finset Var} {s t : Exp} {E : Problem} {θ : Subst} (h : Inv V ((s, t) :: E) θ)
    {v : Var} {e : Exp} (hv : v ∈ Problem.vars ((s, t) :: E)) (hev : e.vars ⊆ Problem.vars ((s, t) :: E))
    (hve : v ∉ e.vars) (hfit : v.ty.fits e.ty) (hname : v.ty.name = true → e.IsName) :
    Inv V (bindIn v e E) (Unify.bind v e θ) := by
  have hdom : (Unify.bind v e θ).dom ⊆ {v} ∪ θ.dom :=
    subset_trans (comp_dom_subset _ _) (Finset.union_subset_union (single_dom_subset v e) (subset_refl _))
  have hvars : Problem.vars (bindIn v e E) ⊆ (Problem.vars E \ {v}) ∪ e.vars := vars_bindIn_subset v e E
  have hE : Problem.vars E ⊆ Problem.vars ((s, t) :: E) := by
    rw [Problem.vars_cons]; exact Finset.subset_union_right
  have hvdom : v ∉ θ.dom := fun hvd => h.apart v hvd hv
  have hθv : θ.f v = .var v := Subst.f_eq_of_not_mem hvdom
  have himg : ∀ u, ((Unify.bind v e θ).f u).vars ⊆ ((θ.f u).vars \ {v}) ∪ e.vars := fun u => by
    show ((Subst.single v e).apply (θ.f u)).vars ⊆ _
    exact vars_single_apply v e (θ.f u)
  exact {
    typed := Subst.Typed.comp (single_typed hfit hname) h.typed
    sep := fun u hu w hw hw' => by
      rcases Finset.mem_union.1 (himg u hw) with hw1 | hw1
      · have hwv : w ≠ v := fun hwv => (Finset.mem_sdiff.1 hw1).2 (by simp [hwv])
        rcases Finset.mem_union.1 (hdom hu) with hu1 | hu1
        · have huv : u = v := by simpa using hu1
          subst huv
          rw [hθv] at hw1
          simp [Exp.vars] at hw1
        · rcases Finset.mem_union.1 (hdom hw') with hw2 | hw2
          · exact hwv (by simpa using hw2)
          · exact h.sep u hu1 w (Finset.mem_sdiff.1 hw1).1 hw2
      · rcases Finset.mem_union.1 (hdom hw') with hw2 | hw2
        · have hwv : w = v := by simpa using hw2
          exact hve (hwv ▸ hw1)
        · exact h.apart w hw2 (hev hw1)
    apart := fun u hu hmem => by
      rcases Finset.mem_union.1 (hvars hmem) with hm | hm
      · rcases Finset.mem_union.1 (hdom hu) with hu1 | hu1
        · exact (Finset.mem_sdiff.1 hm).2 (by simpa using hu1)
        · exact h.apart u hu1 (hE (Finset.mem_sdiff.1 hm).1)
      · rcases Finset.mem_union.1 (hdom hu) with hu1 | hu1
        · have huv : u = v := by simpa using hu1
          exact hve (huv ▸ hm)
        · exact h.apart u hu1 (hev hm)
    evars := fun w hw => by
      rcases Finset.mem_union.1 (hvars hw) with hm | hm
      · exact h.evars (hE (Finset.mem_sdiff.1 hm).1)
      · exact h.evars (hev hm)
    dom_sub := fun u hu => by
      rcases Finset.mem_union.1 (hdom hu) with hu1 | hu1
      · have huv : u = v := by simpa using hu1
        rw [huv]; exact h.evars hv
      · exact h.dom_sub hu1
    range_sub := fun u w hw => by
      rcases Finset.mem_union.1 (himg u hw) with hw1 | hw1
      · exact h.range_sub u w (Finset.mem_sdiff.1 hw1).1
      · exact Or.inl (h.evars (hev hw1)) }

/-! ### Soundness of the algorithm -/

/-- After a binding step, what the result gives for the equations left and the new
substitution, it gives for the equations before and the old one. -/
theorem bind_sound {s t : Exp} {E : Problem} {θ : Subst} {v : Var} {e : Exp}
    (hst : (s = .var v ∧ t = e) ∨ (s = e ∧ t = .var v)) (hθv : θ.f v = .var v) (hve : e ≠ .var v)
    {θ' : Subst} (hS : Solves θ' (bindIn v e E)) (hA : θ'.comp (Unify.bind v e θ) = θ') :
    Solves θ' ((s, t) :: E) ∧ θ'.comp θ = θ' := by
  -- the result solves the binding
  have hvσ : θ'.apply (.var v) = θ'.apply e := by
    have h1 : (Unify.bind v e θ).f v = e := by
      show (Subst.single v e).apply (θ.f v) = e
      rw [hθv, Subst.apply_var, single_f, ite_eq_left rfl]
    have h2 := congrArg (fun τ => τ.f v) hA
    simp only [Subst.comp, h1] at h2
    rw [Subst.apply_var]
    exact h2.symm
  have hσ : θ'.comp (Subst.single v e) = θ' := comp_single_eq (by simpa using hvσ)
  refine ⟨?_, ?_⟩
  · rw [solves_cons]
    refine ⟨?_, ?_⟩
    · rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hvσ
      · exact hvσ.symm
    · intro p hp
      have := hS _ (List.mem_map_of_mem (f := fun p => ((Subst.single v e).apply p.1, (Subst.single v e).apply p.2)) hp)
      simp only at this
      rw [apply_single_apply hσ, apply_single_apply hσ] at this
      exact this
  · calc θ'.comp θ = (θ'.comp (Subst.single v e)).comp θ := by rw [hσ]
      _ = θ'.comp ((Subst.single v e).comp θ) := Subst.comp_assoc _ _ _
      _ = θ' := hA

theorem go_sound (V : Finset Var) : ∀ (E : Problem) (θ : Subst), Inv V E θ → ∀ θ', go E θ = some θ' →
    Solves θ' E ∧ θ'.comp θ = θ' ∧ Inv V [] θ' := by
  intro E θ
  induction E, θ using go.induct with
  | case1 θ =>
    intro hinv θ' hgo
    rw [go] at hgo
    obtain rfl := Option.some.inj hgo
    exact ⟨fun p hp => by simp at hp, idem_of_sep hinv.sep, hinv.sub (by simp [Problem.vars])⟩
  | case2 E θ w ih =>
    intro hinv θ' hgo
    rw [go, ite_eq_left rfl] at hgo
    obtain ⟨h1, h2, h3⟩ := ih hinv.drop θ' hgo
    exact ⟨(solves_cons _ _ _).2 ⟨rfl, h1⟩, h2, h3⟩
  | case3 E θ v w hvw hfit ih =>
    intro hinv θ' hgo
    rw [go, ite_eq_right hvw, ite_eq_left hfit] at hgo
    have hv : v ∈ Problem.vars ((Exp.var v, Exp.var w) :: E) := by simp [Problem.vars_cons, Exp.vars]
    obtain ⟨h1, h2, h3⟩ := ih (hinv.bind hv (by simp [Problem.vars_cons, Exp.vars]) (by simp [Exp.vars, hvw])
      hfit.1 (fun hn => trivial)) θ' hgo
    have hθv : θ.f v = .var v := Subst.f_eq_of_not_mem (fun hd => hinv.apart v hd hv)
    obtain ⟨h4, h5⟩ := bind_sound (Or.inl ⟨rfl, rfl⟩) hθv (by simp [Ne.symm hvw]) h1 h2
    exact ⟨h4, h5, h3⟩
  | case4 E θ v w hvw hfit hfit' ih =>
    intro hinv θ' hgo
    rw [go, ite_eq_right hvw, ite_eq_right hfit, ite_eq_left hfit'] at hgo
    have hw : w ∈ Problem.vars ((Exp.var v, Exp.var w) :: E) := by simp [Problem.vars_cons, Exp.vars]
    obtain ⟨h1, h2, h3⟩ := ih (hinv.bind hw (by simp [Problem.vars_cons, Exp.vars]) (by simp [Exp.vars, Ne.symm hvw])
      hfit' (fun hn => trivial)) θ' hgo
    have hθw : θ.f w = .var w := Subst.f_eq_of_not_mem (fun hd => hinv.apart w hd hw)
    obtain ⟨h4, h5⟩ := bind_sound (Or.inr ⟨rfl, rfl⟩) hθw (by simp [hvw]) h1 h2
    exact ⟨h4, h5, h3⟩
  | case5 E θ v w hvw hfit hfit' =>
    intro hinv θ' hgo
    rw [go, ite_eq_right hvw, ite_eq_right hfit, ite_eq_right hfit'] at hgo
    simp at hgo
  | case6 E θ v k t hfit ih =>
    intro hinv θ' hgo
    rw [go, ite_eq_left hfit] at hgo
    have hv : v ∈ Problem.vars ((Exp.var v, Exp.const k t) :: E) := by simp [Problem.vars_cons, Exp.vars]
    obtain ⟨h1, h2, h3⟩ := ih (hinv.bind hv (by simp [Exp.vars]) (by simp [Exp.vars]) hfit (fun _ => trivial)) θ' hgo
    have hθv : θ.f v = .var v := Subst.f_eq_of_not_mem (fun hd => hinv.apart v hd hv)
    obtain ⟨h4, h5⟩ := bind_sound (Or.inl ⟨rfl, rfl⟩) hθv (by simp) h1 h2
    exact ⟨h4, h5, h3⟩
  | case7 E θ v k t hfit =>
    intro hinv θ' hgo
    rw [go, ite_eq_right hfit] at hgo
    simp at hgo
  | case8 E θ k t v hfit ih =>
    intro hinv θ' hgo
    rw [go, ite_eq_left hfit] at hgo
    have hv : v ∈ Problem.vars ((Exp.const k t, Exp.var v) :: E) := by simp [Problem.vars_cons, Exp.vars]
    obtain ⟨h1, h2, h3⟩ := ih (hinv.bind hv (by simp [Exp.vars]) (by simp [Exp.vars]) hfit (fun _ => trivial)) θ' hgo
    have hθv : θ.f v = .var v := Subst.f_eq_of_not_mem (fun hd => hinv.apart v hd hv)
    obtain ⟨h4, h5⟩ := bind_sound (Or.inr ⟨rfl, rfl⟩) hθv (by simp) h1 h2
    exact ⟨h4, h5, h3⟩
  | case9 E θ k t v hfit =>
    intro hinv θ' hgo
    rw [go, ite_eq_right hfit] at hgo
    simp at hgo
  | case10 E θ v f t args hc ih =>
    intro hinv θ' hgo
    rw [go, ite_eq_left hc] at hgo
    have hv : v ∈ Problem.vars ((Exp.var v, Exp.app f t args) :: E) := by simp [Problem.vars_cons, Exp.vars]
    obtain ⟨h1, h2, h3⟩ := ih (hinv.bind hv (by intro w hw; rw [Problem.vars_cons]; exact Finset.mem_union_left _ (Finset.mem_union_right _ hw))
      hc.2.1 hc.1 (fun hn => by rw [hc.2.2] at hn; exact Bool.noConfusion hn)) θ' hgo
    have hθv : θ.f v = .var v := Subst.f_eq_of_not_mem (fun hd => hinv.apart v hd hv)
    obtain ⟨h4, h5⟩ := bind_sound (Or.inl ⟨rfl, rfl⟩) hθv (by simp) h1 h2
    exact ⟨h4, h5, h3⟩
  | case11 E θ v f t args hc =>
    intro hinv θ' hgo
    rw [go, ite_eq_right hc] at hgo
    simp at hgo
  | case12 E θ f t args v hc ih =>
    intro hinv θ' hgo
    rw [go, ite_eq_left hc] at hgo
    have hv : v ∈ Problem.vars ((Exp.app f t args, Exp.var v) :: E) := by simp [Problem.vars_cons, Exp.vars]
    obtain ⟨h1, h2, h3⟩ := ih (hinv.bind hv (by intro w hw; rw [Problem.vars_cons]; exact Finset.mem_union_left _ (Finset.mem_union_left _ hw))
      hc.2.1 hc.1 (fun hn => by rw [hc.2.2] at hn; exact Bool.noConfusion hn)) θ' hgo
    have hθv : θ.f v = .var v := Subst.f_eq_of_not_mem (fun hd => hinv.apart v hd hv)
    obtain ⟨h4, h5⟩ := bind_sound (Or.inr ⟨rfl, rfl⟩) hθv (by simp) h1 h2
    exact ⟨h4, h5, h3⟩
  | case13 E θ f t args v hc =>
    intro hinv θ' hgo
    rw [go, ite_eq_right hc] at hgo
    simp at hgo
  | case14 E θ k t k' t' hc ih =>
    intro hinv θ' hgo
    rw [go, ite_eq_left hc] at hgo
    obtain ⟨rfl, rfl⟩ := hc
    obtain ⟨h1, h2, h3⟩ := ih hinv.drop θ' hgo
    exact ⟨(solves_cons _ _ _).2 ⟨rfl, h1⟩, h2, h3⟩
  | case15 E θ k t k' t' hc =>
    intro hinv θ' hgo
    rw [go, ite_eq_right hc] at hgo
    simp at hgo
  | case16 E θ f t args f' t' args' hc ih =>
    intro hinv θ' hgo
    rw [go, ite_eq_left hc] at hgo
    obtain ⟨rfl, rfl, hlen⟩ := hc
    obtain ⟨h1, h2, h3⟩ := ih hinv.zip θ' hgo
    rw [solves_append] at h1
    refine ⟨(solves_cons _ _ _).2 ⟨?_, h1.2⟩, h2, h3⟩
    simp only [Subst.apply]
    rw [applyList_eq_of_solves_zip θ' args args' hlen h1.1]
  | case17 E θ f t args f' t' args' hc =>
    intro hinv θ' hgo
    rw [go, ite_eq_right hc] at hgo
    simp at hgo
  | case18 s t E θ h1 h2 h3 h4 h5 h6 h7 =>
    intro hinv θ' hgo
    cases s <;> cases t
    · exact (h1 _ _ rfl rfl).elim
    · exact (h2 _ _ _ rfl rfl).elim
    · exact (h4 _ _ _ _ rfl rfl).elim
    · exact (h3 _ _ _ rfl rfl).elim
    · exact (h6 _ _ _ _ rfl rfl).elim
    · rw [go.eq_def] at hgo; simp at hgo
    · exact (h5 _ _ _ _ rfl rfl).elim
    · rw [go.eq_def] at hgo; simp at hgo
    · exact (h7 _ _ _ _ _ _ rfl rfl).elim

/-! ### Completeness of the algorithm -/

/-- Before a binding step, a solution of the equations that absorbs the substitution
solves the equations after it and absorbs the new substitution. -/
theorem bind_complete {s t : Exp} {E : Problem} {θ : Subst} {v : Var} {e : Exp}
    (hst : (s = .var v ∧ t = e) ∨ (s = e ∧ t = .var v)) (hve : e ≠ .var v)
    {ρ : Subst} (hS : Solves ρ ((s, t) :: E)) (hA : ρ.comp θ = ρ) :
    Solves ρ (bindIn v e E) ∧ ρ.comp (Unify.bind v e θ) = ρ := by
  rw [solves_cons] at hS
  have hvσ : ρ.apply (.var v) = ρ.apply e := by
    rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hS.1
    · exact hS.1.symm
  have hσ : ρ.comp (Subst.single v e) = ρ := comp_single_eq (by simpa using hvσ)
  refine ⟨?_, ?_⟩
  · intro p hp
    simp only [bindIn, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    simp only
    rw [apply_single_apply hσ, apply_single_apply hσ]
    exact hS.2 q hq
  · show ρ.comp ((Subst.single v e).comp θ) = ρ
    rw [← Subst.comp_assoc, hσ, hA]

theorem go_complete (V : Finset Var) : ∀ (E : Problem) (θ : Subst), Inv V E θ →
    ∀ ρ : Subst, ρ.Typed → Solves ρ E → ρ.comp θ = ρ → ∃ θ', go E θ = some θ' ∧ ρ.IsInstance θ' := by
  intro E θ
  induction E, θ using go.induct with
  | case1 θ =>
    intro _ ρ _ _ hA
    exact ⟨θ, by rw [go], ⟨ρ, hA.symm⟩⟩
  | case2 E θ w ih =>
    intro hinv ρ hρ hS hA
    rw [solves_cons] at hS
    obtain ⟨θ', hgo, hi⟩ := ih hinv.drop ρ hρ hS.2 hA
    exact ⟨θ', by rw [go, ite_eq_left rfl]; exact hgo, hi⟩
  | case3 E θ v w hvw hfit ih =>
    intro hinv ρ hρ hS hA
    have hv : v ∈ Problem.vars ((Exp.var v, Exp.var w) :: E) := by simp [Problem.vars_cons, Exp.vars]
    obtain ⟨hS', hA'⟩ := bind_complete (Or.inl ⟨rfl, rfl⟩) (by simp [Ne.symm hvw]) hS hA
    obtain ⟨θ', hgo, hi⟩ := ih (hinv.bind hv (by simp [Problem.vars_cons, Exp.vars]) (by simp [Exp.vars, hvw])
      hfit.1 (fun _ => trivial)) ρ hρ hS' hA'
    exact ⟨θ', by rw [go, ite_eq_right hvw, ite_eq_left hfit]; exact hgo, hi⟩
  | case4 E θ v w hvw hfit hfit' ih =>
    intro hinv ρ hρ hS hA
    have hw : w ∈ Problem.vars ((Exp.var v, Exp.var w) :: E) := by simp [Problem.vars_cons, Exp.vars]
    obtain ⟨hS', hA'⟩ := bind_complete (Or.inr ⟨rfl, rfl⟩) (by simp [hvw]) hS hA
    obtain ⟨θ', hgo, hi⟩ := ih (hinv.bind hw (by simp [Problem.vars_cons, Exp.vars]) (by simp [Exp.vars, Ne.symm hvw])
      hfit' (fun _ => trivial)) ρ hρ hS' hA'
    exact ⟨θ', by rw [go, ite_eq_right hvw, ite_eq_right hfit, ite_eq_left hfit']; exact hgo, hi⟩
  | case5 E θ v w hvw hfit hfit' =>
    intro hinv ρ hρ hS hA
    exfalso
    rw [solves_cons] at hS
    have heq : ρ.f v = ρ.f w := by simpa [Subst.apply_var] using hS.1
    have h1 := (hρ v).1
    have h2 := (hρ w).1
    rw [heq] at h1
    have hfit0 : ¬ v.ty.fits w.ty := fun h => hfit ⟨h, Or.inr hfit'⟩
    clear hfit
    simp only [Ty.fits] at h1 h2 hfit0 hfit'
    have hsort : v.ty.sort = w.ty.sort := h1.1.trans h2.1.symm
    cases hvn : v.ty.name <;> cases hwn : w.ty.name <;> simp_all
  | case6 E θ v k t hfit ih =>
    intro hinv ρ hρ hS hA
    have hv : v ∈ Problem.vars ((Exp.var v, Exp.const k t) :: E) := by simp [Problem.vars_cons, Exp.vars]
    obtain ⟨hS', hA'⟩ := bind_complete (Or.inl ⟨rfl, rfl⟩) (by simp) hS hA
    obtain ⟨θ', hgo, hi⟩ := ih (hinv.bind hv (by simp [Exp.vars]) (by simp [Exp.vars]) hfit (fun _ => trivial)) ρ hρ hS' hA'
    exact ⟨θ', by rw [go, ite_eq_left hfit]; exact hgo, hi⟩
  | case7 E θ v k t hfit =>
    intro hinv ρ hρ hS hA
    exfalso
    rw [solves_cons] at hS
    have heq : ρ.f v = .const k t := by simpa [Subst.apply] using hS.1
    have h1 := (hρ v).1
    rw [heq] at h1
    exact hfit h1
  | case8 E θ k t v hfit ih =>
    intro hinv ρ hρ hS hA
    have hv : v ∈ Problem.vars ((Exp.const k t, Exp.var v) :: E) := by simp [Problem.vars_cons, Exp.vars]
    obtain ⟨hS', hA'⟩ := bind_complete (Or.inr ⟨rfl, rfl⟩) (by simp) hS hA
    obtain ⟨θ', hgo, hi⟩ := ih (hinv.bind hv (by simp [Exp.vars]) (by simp [Exp.vars]) hfit (fun _ => trivial)) ρ hρ hS' hA'
    exact ⟨θ', by rw [go, ite_eq_left hfit]; exact hgo, hi⟩
  | case9 E θ k t v hfit =>
    intro hinv ρ hρ hS hA
    exfalso
    rw [solves_cons] at hS
    have heq : ρ.f v = .const k t := by simpa [Subst.apply] using hS.1.symm
    have h1 := (hρ v).1
    rw [heq] at h1
    exact hfit h1
  | case10 E θ v f t args hc ih =>
    intro hinv ρ hρ hS hA
    have hv : v ∈ Problem.vars ((Exp.var v, Exp.app f t args) :: E) := by simp [Problem.vars_cons, Exp.vars]
    obtain ⟨hS', hA'⟩ := bind_complete (Or.inl ⟨rfl, rfl⟩) (by simp) hS hA
    obtain ⟨θ', hgo, hi⟩ := ih (hinv.bind hv (by intro w hw; rw [Problem.vars_cons]; exact Finset.mem_union_left _ (Finset.mem_union_right _ hw))
      hc.2.1 hc.1 (fun hn => by rw [hc.2.2] at hn; exact Bool.noConfusion hn)) ρ hρ hS' hA'
    exact ⟨θ', by rw [go, ite_eq_left hc]; exact hgo, hi⟩
  | case11 E θ v f t args hc =>
    intro hinv ρ hρ hS hA
    exfalso
    rw [solves_cons] at hS
    have heq : ρ.f v = ρ.apply (.app f t args) := by simpa [Subst.apply_var] using hS.1
    apply hc
    refine ⟨?_, ?_, ?_⟩
    · have h1 := (hρ v).1
      rw [heq] at h1
      simpa [Subst.apply, Exp.ty] using h1
    · intro hmem
      have := size_lt_of_mem_vars_app ρ f t args v hmem
      rw [heq] at this
      exact lt_irrefl _ this
    · by_contra hn
      have hn' : v.ty.name = true := by simpa using hn
      have := (hρ v).2 hn'
      rw [heq] at this
      simp [Subst.apply, Exp.IsName] at this
  | case12 E θ f t args v hc ih =>
    intro hinv ρ hρ hS hA
    have hv : v ∈ Problem.vars ((Exp.app f t args, Exp.var v) :: E) := by simp [Problem.vars_cons, Exp.vars]
    obtain ⟨hS', hA'⟩ := bind_complete (Or.inr ⟨rfl, rfl⟩) (by simp) hS hA
    obtain ⟨θ', hgo, hi⟩ := ih (hinv.bind hv (by intro w hw; rw [Problem.vars_cons]; exact Finset.mem_union_left _ (Finset.mem_union_left _ hw))
      hc.2.1 hc.1 (fun hn => by rw [hc.2.2] at hn; exact Bool.noConfusion hn)) ρ hρ hS' hA'
    exact ⟨θ', by rw [go, ite_eq_left hc]; exact hgo, hi⟩
  | case13 E θ f t args v hc =>
    intro hinv ρ hρ hS hA
    exfalso
    rw [solves_cons] at hS
    have heq : ρ.f v = ρ.apply (.app f t args) := by simpa [Subst.apply_var] using hS.1.symm
    apply hc
    refine ⟨?_, ?_, ?_⟩
    · have h1 := (hρ v).1
      rw [heq] at h1
      simpa [Subst.apply, Exp.ty] using h1
    · intro hmem
      have := size_lt_of_mem_vars_app ρ f t args v hmem
      rw [heq] at this
      exact lt_irrefl _ this
    · by_contra hn
      have hn' : v.ty.name = true := by simpa using hn
      have := (hρ v).2 hn'
      rw [heq] at this
      simp [Subst.apply, Exp.IsName] at this
  | case14 E θ k t k' t' hc ih =>
    intro hinv ρ hρ hS hA
    rw [solves_cons] at hS
    obtain ⟨θ', hgo, hi⟩ := ih hinv.drop ρ hρ hS.2 hA
    exact ⟨θ', by rw [go, ite_eq_left hc]; exact hgo, hi⟩
  | case15 E θ k t k' t' hc =>
    intro hinv ρ hρ hS hA
    exfalso
    rw [solves_cons] at hS
    simp [Subst.apply] at hS
    exact hc ⟨hS.1.1, hS.1.2⟩
  | case16 E θ f t args f' t' args' hc ih =>
    intro hinv ρ hρ hS hA
    rw [solves_cons] at hS
    obtain ⟨rfl, rfl, hlen⟩ := hc
    have hS' : Solves ρ (args.zip args' ++ E) := by
      rw [solves_append]
      refine ⟨?_, hS.2⟩
      simp only [Subst.apply, Exp.app.injEq, true_and] at hS
      exact solves_zip_of_applyList_eq ρ args args' hlen hS.1
    obtain ⟨θ', hgo, hi⟩ := ih hinv.zip ρ hρ hS' hA
    exact ⟨θ', by rw [go, ite_eq_left ⟨rfl, rfl, hlen⟩]; exact hgo, hi⟩
  | case17 E θ f t args f' t' args' hc =>
    intro hinv ρ hρ hS hA
    exfalso
    rw [solves_cons] at hS
    simp only [Subst.apply, Exp.app.injEq] at hS
    apply hc
    refine ⟨hS.1.1, hS.1.2.1, ?_⟩
    have := congrArg List.length hS.1.2.2
    rwa [length_applyList, length_applyList] at this
  | case18 s t E θ h1 h2 h3 h4 h5 h6 h7 =>
    intro hinv ρ hρ hS hA
    exfalso
    rw [solves_cons] at hS
    cases s <;> cases t
    · exact h1 _ _ rfl rfl
    · exact h2 _ _ _ rfl rfl
    · exact h4 _ _ _ _ rfl rfl
    · exact h3 _ _ _ rfl rfl
    · exact h6 _ _ _ _ rfl rfl
    · simp [Subst.apply] at hS
    · exact h5 _ _ _ _ rfl rfl
    · simp [Subst.apply] at hS
    · exact h7 _ _ _ _ _ _ rfl rfl

end Unify

/-- The postulate, discharged for the first-order unifier. -/
def Unify.postulate : Unification where
  mgu := Unify.mgu
  typed := fun E θ h => (Unify.go_sound E.vars E Subst.id (Unify.Inv.init E) θ h).2.2.typed
  idem := fun E θ h => Unify.idem_of_sep (Unify.go_sound E.vars E Subst.id (Unify.Inv.init E) θ h).2.2.sep
  solves := fun E θ h => (Unify.go_sound E.vars E Subst.id (Unify.Inv.init E) θ h).1
  mostGeneral := fun E σ hσ hs => Unify.go_complete E.vars E Subst.id (Unify.Inv.init E) σ hσ hs (Subst.comp_id σ)
  dom_sub := fun E θ h _ hv => (Unify.go_sound E.vars E Subst.id (Unify.Inv.init E) θ h).2.2.dom_sub hv
  range_sub := fun E θ h v w hw => (Unify.go_sound E.vars E Subst.id (Unify.Inv.init E) θ h).2.2.range_sub v w hw

end Theory
