/-
From a proof over the extended database to an MM0 proof (`docs/THEORY.md`,
"Definitions", milestone 9): the lemmas about the rules and the translation `toD`,
and its theorem, `toD_isProof` — a proof of the statement over `db.withConv L` stands
for an MM0 proof of the statement over `db`.
-/
import Theory.Rules
import Theory.Generality

namespace Theory

/-! ### Substitutions on applications and judgments -/

theorem Subst.applyList_eq_map (θ : Subst) : ∀ es : List Exp, θ.applyList es = es.map θ.apply
  | [] => rfl
  | e :: es => by simp [Subst.applyList, Subst.applyList_eq_map θ es]

theorem Subst.apply_app (θ : Subst) (f : ℕ) (t : Ty) (args : List Exp) :
    θ.apply (.app f t args) = .app f t (args.map θ.apply) := by
  simp [Subst.apply, Subst.applyList_eq_map]

theorem Subst.sort_apply {θ : Subst} (hθ : θ.Typed) (e : Exp) : (θ.apply e).ty.sort = e.ty.sort :=
  (Subst.ty_apply hθ e).1.symm

namespace Language

theorem eq_ty (L : Language) (s : ℕ) (strict : Bool) (a b : Exp) : (L.eq s strict a b).ty = L.judgTy := rfl

theorem eq_inj {L : Language} {s s' : ℕ} {strict strict' : Bool} {a b a' b' : Exp}
    (h : L.eq s strict a b = L.eq s' strict' a' b') : a = a' ∧ b = b' := by
  simp only [Language.eq, Exp.app.injEq, List.cons.injEq, and_true] at h
  exact ⟨h.2.2.1, h.2.2.2⟩

theorem apply_eq (L : Language) (θ : Subst) (s : ℕ) (strict : Bool) (a b : Exp) :
    θ.apply (L.eq s strict a b) = L.eq s strict (θ.apply a) (θ.apply b) := by
  simp [Language.eq, Subst.apply_app]

theorem vars_eq (L : Language) (s : ℕ) (strict : Bool) (a b : Exp) :
    (L.eq s strict a b).vars = a.vars ∪ b.vars := by
  simp [Language.eq, Exp.vars, Exp.varsList]

end Language

/-! ### The extended database by index -/

namespace Database

variable (L : Language) (db : Database)

theorem withConv_length : (db.withConv L).asserts.length = db.asserts.length + (Rules.all L db.defs).length := by
  simp [Database.withConv]

theorem withConv_getElem?_lt {a : ℕ} (h : a < db.asserts.length) :
    (db.withConv L).asserts[a]? = db.asserts[a]? := by
  simp [Database.withConv, List.getElem?_append, h]

theorem ruleAt_of_lt {a : ℕ} (h : a < db.asserts.length) : db.ruleAt L a = none := by
  simp [Database.ruleAt, h]

/-- What a rule of each kind is: by the construction of `Rules.all`. -/
def RuleSpec (defs : List Def) : RuleKind → Assertion → Prop
  | .refl s, A => A = Rules.reflRule L s ∧ s < L.sorts
  | .conv s, A => A = Rules.convRule L s ∧ s < L.sorts
  | .cong t sa, A => A = Rules.congRule L t sa ∧ t < L.terms
  | .unfold d strict, A => ∃ D, defs[d]? = some D ∧ A = Rules.unfoldRule L D strict
  | .fold d strict, A => ∃ D, defs[d]? = some D ∧ A = Rules.foldRule L D strict

theorem mem_all_spec {defs : List Def} {k : RuleKind} {A : Assertion}
    (h : (k, A) ∈ Rules.all L defs) : RuleSpec L defs k A := by
  simp only [Rules.all, List.mem_append, Rules.sortRules, Rules.termRules, Rules.defRules,
    List.mem_flatMap, List.mem_range, List.mem_cons] at h
  rcases h with (⟨s, hs, h⟩ | ⟨t, ht, h⟩) | ⟨⟨D, d⟩, hmem, h⟩
  · rcases h with h | h
    · cases h; exact ⟨rfl, hs⟩
    · split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, hs⟩
      · simp at h
  · by_cases hreg : (Rules.regularArgs (L.sig.args t)).isEmpty = true
    · rw [ite_eq_left hreg] at h
      simp at h
    · rw [ite_eq_right hreg] at h
      simp only [List.mem_cons, List.mem_map, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨i, _, rfl, rfl⟩ <;> exact ⟨rfl, ht⟩
  · have hd : defs[d]? = some D := by
      obtain ⟨_, hlt, hD⟩ := List.mem_zipIdx hmem
      simp only [Nat.zero_add, Nat.sub_zero] at hlt hD
      rw [hD]
      exact List.getElem?_eq_getElem hlt
    simp only [Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨D, hd, rfl⟩

theorem ruleAt_some {a : ℕ} {k : RuleKind} (h : db.ruleAt L a = some k) :
    ∃ A, (db.withConv L).asserts[a]? = some A ∧ (k, A) ∈ Rules.all L db.defs := by
  unfold Database.ruleAt at h
  split at h
  · simp at h
  · rename_i hlt
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨k', A⟩, hget, hk⟩ := h
    cases hk
    refine ⟨A, ?_, List.mem_of_getElem? hget⟩
    simp [Database.withConv, List.getElem?_append_right (Nat.le_of_not_lt hlt), hget]

theorem ruleAt_of_getElem? {a : ℕ} {A : Assertion} (hA : (db.withConv L).asserts[a]? = some A)
    (ha : db.asserts.length ≤ a) : ∃ k, db.ruleAt L a = some k ∧ (k, A) ∈ Rules.all L db.defs := by
  simp only [Database.withConv, List.getElem?_append_right ha, List.getElem?_map, Option.map_eq_some_iff] at hA
  obtain ⟨⟨k, A'⟩, hget, hk⟩ := hA
  cases hk
  refine ⟨k, ?_, List.mem_of_getElem? hget⟩
  simp [Database.ruleAt, Nat.not_lt.2 ha, hget]

theorem stepConds_withConv_lt {a : ℕ} (h : a < db.asserts.length) (θ : Subst) :
    stepConds (db.withConv L) a θ = stepConds db a θ := by
  simp [stepConds, withConv_getElem?_lt L db h]

end Database

/-! ### The instance of a definition under a step's substitution -/

namespace Def

theorem find?_zip_map {l : List Var} (g : Var → Exp) {v : Var} (hv : v ∈ l) :
    ∃ p, (l.zip (l.map g)).find? (fun p => decide (p.1 = v)) = some p ∧ p.2 = g v := by
  induction l with
  | nil => simp at hv
  | cons x l ih =>
    simp only [List.map_cons, List.zip_cons_cons]
    by_cases hx : x = v
    · subst hx
      exact ⟨(x, g x), by simp, rfl⟩
    · have hv' : v ∈ l := by
        simp only [List.mem_cons] at hv
        exact hv.resolve_left (Ne.symm hx)
      obtain ⟨p, hp, hp2⟩ := ih hv'
      refine ⟨p, ?_, hp2⟩
      rw [List.find?_cons_of_neg (by simpa using hx), hp]

theorem binding_of_mem (D : Def) (g : Var → Exp) {v : Var} (hv : v ∈ D.args ++ D.dummies) :
    D.binding (D.args.map g) (D.dummies.map g) v = g v := by
  unfold Def.binding
  rw [← List.map_append]
  obtain ⟨p, hp, hp2⟩ := find?_zip_map g hv
  rw [hp]
  exact hp2

/-- The instance that gives the binders what a substitution gives them is that
substitution on the value. -/
theorem inst_apply (D : Def) (hwf : D.WF) (θ : Subst) :
    (D.inst (D.args.map θ.f) (D.dummies.map θ.f)).apply D.value = θ.apply D.value := by
  apply apply_congr_vars
  intro v hv
  have hv' : v ∈ D.args ++ D.dummies := List.mem_toFinset.1 (hwf.value_vars hv)
  show D.binding (D.args.map θ.f) (D.dummies.map θ.f) v = θ.f v
  exact D.binding_of_mem θ.f hv'

end Def

/-! ### Names -/

/-- A name of a name type occurs in itself. -/
theorem Consts.name_mem_self (c : Consts) {e : Exp} (hn : e.IsName) (ht : e.ty.name = true) : e ∈ c.names e := by
  rw [Consts.mem_names]
  cases e with
  | var v => exact Or.inl ⟨v, by simp [Exp.vars], ht, rfl⟩
  | const k t => exact Or.inr (Or.inl ⟨(k, t), by simp [Exp.consts], ht, rfl⟩)
  | app _ _ _ => exact absurd hn (by simp [Exp.IsName])

/-- Pairwise distinct images, from the pairs of each with every later one. -/
theorem Rules.nodup_map_of_laterPairs {ys : List Var} (f : Var → Exp)
    (h : ∀ p ∈ Rules.laterPairs ys, f p.1 ≠ f p.2) : (ys.map f).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  induction ys with
  | nil => simp
  | cons y ys ih =>
    rw [List.pairwise_cons]
    refine ⟨fun y' hy' => h (y, y') ?_, ih fun p hp => h p ?_⟩
    · simp [Rules.laterPairs, hy']
    · simp [Rules.laterPairs, hp]


/-! ### Typing -/

theorem Ty.ext' {a b : Ty} (hs : a.sort = b.sort) (hn : a.name = b.name) : a = b := by
  cases a; cases b; simp_all

theorem Subst.fitsTy_f {θ : Subst} (hθ : θ.Typed) (v : Var) : FitsTy v.ty (θ.f v) :=
  ⟨(hθ v).1, (hθ v).2⟩

/-- A variable of a name type gets a name of that type. -/
theorem Subst.ty_f_of_name {θ : Subst} (hθ : θ.Typed) {y : Var} (hy : y.ty.name = true) : (θ.f y).ty = y.ty := by
  obtain ⟨hs, hn⟩ := (hθ y).1
  exact Ty.ext' hs.symm (by rw [hn hy, hy])

theorem List.forall₂_map_self {α β : Type} {P : α → β → Prop} {g : α → β} :
    ∀ l : List α, (∀ x ∈ l, P x (g x)) → List.Forall₂ P l (l.map g)
  | [], _ => List.Forall₂.nil
  | x :: l, h => List.Forall₂.cons (h x (by simp)) (List.forall₂_map_self l fun y hy => h y (by simp [hy]))

theorem Rules.mem_laterPairs {p : Var × Var} : ∀ {ys : List Var}, p ∈ Rules.laterPairs ys → p.1 ∈ ys ∧ p.2 ∈ ys
  | [], h => by simp [Rules.laterPairs] at h
  | y :: ys, h => by
    simp only [Rules.laterPairs, List.mem_append, List.mem_map] at h
    rcases h with ⟨y', hy', rfl⟩ | h
    · exact ⟨by simp, by simp [hy']⟩
    · obtain ⟨h1, h2⟩ := Rules.mem_laterPairs h
      exact ⟨by simp [h1], by simp [h2]⟩

/-- The language fits the database and the statement: the judgment sort is none of the
file's sorts, and no assertion, hypothesis or conclusion is a judgment at its root. -/
structure Language.WF (L : Language) (db : Database) (st : Statement) : Prop where
  sorts_le : L.sorts ≤ L.judg
  assert_sort : ∀ A ∈ db.asserts, A.concl.ty.sort ≠ L.judg ∧ ∀ h ∈ A.hyps, h.ty.sort ≠ L.judg
  st_sort : st.concl.ty.sort ≠ L.judg ∧ ∀ h ∈ st.hyps, h.ty.sort ≠ L.judg

theorem condsHold_of_mem {db : Database} {st : Statement} {e : Exp} {a : ℕ} {θ : Subst} {cs : List PTree}
    (hc : CondsHold db st (.step e a θ cs)) {c : PTree} (hmem : c ∈ cs) : CondsHold db st c := by
  intro k hk
  exact hc k (by simp only [PTree.conds, List.mem_append]; exact Or.inr ((PTree.mem_condsList db cs k).2 ⟨c, hmem, hk⟩))

theorem stepConds_hold {db : Database} {st : Statement} {e : Exp} {a : ℕ} {θ : Subst} {cs : List PTree}
    (hc : CondsHold db st (.step e a θ cs)) : ∀ k ∈ stepConds db a θ, k.Holds st.consts := by
  intro k hk
  exact hc k (by simp only [PTree.conds, List.mem_append]; exact Or.inl hk)

/-! ### The congruence rule -/

section Cong

variable {L : Language} {db : Database} {st : Statement}

theorem congVars_fits {θ : Subst} (hθ : θ.Typed) :
    ∀ (tys : List Ty) (k : ℕ),
      List.Forall₂ FitsTy tys ((Rules.congVars tys k).2.1.map θ.apply) ∧
      List.Forall₂ FitsTy tys ((Rules.congVars tys k).2.2.map θ.apply)
  | [], _ => ⟨List.Forall₂.nil, List.Forall₂.nil⟩
  | ty :: tys, k => by
    by_cases hn : ty.name = true
    · simp only [Rules.congVars, hn, ite_true, List.map_cons, Rules.v, Subst.apply_var]
      exact ⟨List.Forall₂.cons (Subst.fitsTy_f hθ ⟨k, ty⟩) (congVars_fits hθ tys (k + 1)).1,
        List.Forall₂.cons (Subst.fitsTy_f hθ ⟨k, ty⟩) (congVars_fits hθ tys (k + 1)).2⟩
    · simp only [Rules.congVars, hn, Bool.false_eq_true, ite_false, List.map_cons, Rules.v, Subst.apply_var]
      exact ⟨List.Forall₂.cons (Subst.fitsTy_f hθ ⟨k, ty⟩) (congVars_fits hθ tys (k + 2)).1,
        List.Forall₂.cons (Subst.fitsTy_f hθ ⟨k + 1, ty⟩) (congVars_fits hθ tys (k + 2)).2⟩

theorem congVars_names (θ : Subst) :
    ∀ (tys : List Ty) (k i : ℕ) (u : Ty), tys[i]? = some u → u.name = true →
      ((Rules.congVars tys k).2.1.map θ.apply)[i]? = ((Rules.congVars tys k).2.2.map θ.apply)[i]?
  | [], _, i, _, h, _ => by simp at h
  | ty :: tys, k, 0, u, h, hu => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [Rules.congVars, hu]
  | ty :: tys, k, i + 1, u, h, hu => by
    simp only [List.getElem?_cons_succ] at h
    by_cases hn : ty.name = true
    · simp only [Rules.congVars, hn, ite_true, List.map_cons, List.getElem?_cons_succ]
      exact congVars_names θ tys (k + 1) i u h hu
    · simp only [Rules.congVars, hn, Bool.false_eq_true, ite_false, List.map_cons, List.getElem?_cons_succ]
      exact congVars_names θ tys (k + 2) i u h hu

/-- The certificates of the arguments of a congruence step are valid: at an argument
that takes names, reflexivity; at the others, the children's. -/
theorem congList_valid {θ : Subst} (sa : Option ℕ) :
    ∀ (tys : List Ty) (k i : ℕ) (cs : List PTree),
      cs.map PTree.expr =
        (Rules.congHyps L sa tys (Rules.congVars tys k).2.1 (Rules.congVars tys k).2.2 i).map θ.apply →
      (∀ c ∈ cs, ∀ (s : ℕ) (strict : Bool) (a b : Exp), c.expr = L.eq s strict a b →
        CValid db L.sig st.consts (c.toC L db) a b) →
      CValidList db L.sig st.consts (Translate.congCerts θ tys (PTree.toCList L db cs) k)
        ((Rules.congVars tys k).2.1.map θ.apply) ((Rules.congVars tys k).2.2.map θ.apply)
  | [], k, i, cs, hcs, _ => by
    simp only [Rules.congVars, Rules.congHyps, List.map_nil] at hcs ⊢
    rw [List.map_eq_nil_iff.1 hcs]
    simp only [Translate.congCerts]
    exact CValidList.nil
  | ty :: tys, k, i, cs, hcs, ih => by
    by_cases hn : ty.name = true
    · simp only [Rules.congVars, hn, ite_true, Rules.congHyps, List.nil_append] at hcs ⊢
      simp only [Translate.congCerts, hn, ite_true, List.map_cons, Rules.v, Subst.apply_var]
      exact CValidList.cons (CValid.refl _) (congList_valid sa tys (k + 1) (i + 1) cs hcs ih)
    · simp only [Rules.congVars, hn, Bool.false_eq_true, ite_false, Rules.congHyps, List.singleton_append, List.map_cons] at hcs ⊢
      cases cs with
      | nil => simp at hcs
      | cons c cs' =>
        simp only [List.map_cons, List.cons.injEq] at hcs
        obtain ⟨hc, hcs'⟩ := hcs
        simp only [PTree.toCList, Translate.congCerts, hn, Bool.false_eq_true, ite_false, Rules.v, Subst.apply_var]
        refine CValidList.cons ?_ (congList_valid sa tys (k + 2) (i + 1) cs' hcs' fun c' hc' => ih c' (by simp [hc']))
        have := ih c (by simp) ty.sort (sa == some i) (θ.f ⟨k, ty⟩) (θ.f ⟨k + 1, ty⟩)
          (by rw [hc, Language.apply_eq]; simp [Rules.v])
        exact this

end Cong

/-! ### A rule tree proving a judgment stands for a certificate -/

section Cert

variable {L : Language} {db : Database} {st : Statement}

theorem sort_ne_of_eq {e : Exp} {s : ℕ} {strict : Bool} {a b : Exp} (hT : e = L.eq s strict a b) :
    e.ty.sort = L.judg := by
  rw [hT]; rfl

/-- A valid rule tree whose expression is a judgment `a ≡ b` stands for a certificate
from `a` to `b`. -/
theorem cert_valid (hL : L.WF db st) (hdefs : db.DefsWF) {T : PTree} (hs : Shape (db.withConv L) st T) :
    CondsHold (db.withConv L) st T → ∀ (s : ℕ) (strict : Bool) (a b : Exp), T.expr = L.eq s strict a b →
      CValid db L.sig st.consts (T.toC L db) a b := by
  induction hs with
  | hyp h e hh he =>
    intro _ s strict a b hT
    simp only [PTree.expr] at hT
    exfalso
    apply (hL.st_sort.2 st.hyps[h]! (by rw [getElem!_pos st.hyps h hh]; exact List.getElem_mem hh))
    rw [← he]
    exact sort_ne_of_eq hT
  | step e a θ cs A hA hθ hdom he hcs hall ih =>
    intro hc s strict a' b' hT
    simp only [PTree.expr] at hT
    by_cases hlt : a < db.asserts.length
    · -- an assertion of the file concludes no judgment
      exfalso
      rw [Database.withConv_getElem?_lt L db hlt] at hA
      apply (hL.assert_sort A (List.mem_of_getElem? hA)).1
      rw [← Subst.sort_apply hθ A.concl, ← he]
      exact sort_ne_of_eq hT
    · obtain ⟨k, hk, hmem⟩ := Database.ruleAt_of_getElem? L db hA (Nat.le_of_not_lt hlt)
      have hspec := Database.mem_all_spec L hmem
      cases k with
      | refl s' =>
        obtain ⟨rfl, _⟩ := hspec
        simp only [Rules.reflRule, Language.apply_eq, Rules.v, Subst.apply_var] at he
        rw [he] at hT
        obtain ⟨rfl, rfl⟩ := Language.eq_inj hT
        simp only [PTree.toC, hk]
        exact CValid.refl _
      | conv s' =>
        obtain ⟨rfl, hs'⟩ := hspec
        exfalso
        simp only [Rules.convRule, Rules.v, Subst.apply_var] at he
        have h1 : e.ty.sort = s' := by
          rw [he]
          exact ((hθ ⟨0, ⟨s', false⟩⟩).1.1).symm
        have h2 := sort_ne_of_eq hT
        have h3 := hL.sorts_le
        omega
      | cong t sa =>
        obtain ⟨rfl, _⟩ := hspec
        simp only [Rules.congRule, Language.apply_eq, Subst.apply_app] at he hcs
        rw [he] at hT
        obtain ⟨rfl, rfl⟩ := Language.eq_inj hT
        simp only [PTree.toC, hk]
        refine CValid.cong t ⟨L.sig.sort t, false⟩ ?_ (congVars_fits hθ _ 0).1 (congVars_fits hθ _ 0).2
          (congVars_names θ _ 0)
        exact congList_valid sa (L.sig.args t) 0 0 cs hcs fun c hmem s'' strict'' a'' b'' hc' =>
          ih c hmem (condsHold_of_mem hc hmem) s'' strict'' a'' b'' hc'
      | unfold d strict' =>
        obtain ⟨D, hD, rfl⟩ := hspec
        have hwfD : D.WF := hdefs D (List.mem_of_getElem? hD)
        simp only [Rules.unfoldRule, Language.apply_eq, Rules.defApp, Subst.apply_app, List.map_map,
          Function.comp_def, Subst.apply_var, List.map_cons, List.map_nil] at he hcs
        rw [he] at hT
        obtain ⟨rfl, rfl⟩ := Language.eq_inj hT
        cases cs with
        | nil => simp at hcs
        | cons c cs' =>
          cases cs' with
          | cons _ _ => simp at hcs
          | nil =>
            simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcs
            simp only [PTree.toC, hk, hD, PTree.toCList, List.headD_cons]
            have hconds := stepConds_hold hc
            simp only [stepConds, hA, Rules.unfoldRule] at hconds
            refine CValid.trans (e := θ.apply D.value) ?_
              (ih c (by simp) (condsHold_of_mem hc (by simp)) _ _ _ _ hcs)
            have h := CValid.unfold (db := db) (sig := L.sig) (c := st.consts) hD
              (List.forall₂_map_self D.args fun x _ => Subst.fitsTy_f hθ x)
              (List.forall₂_map_self D.dummies fun y hy =>
                ⟨(hθ y).2 (hwfD.dummies_name y hy), Subst.ty_f_of_name hθ (hwfD.dummies_name y hy)⟩)
              (fun z hz e' he' => by
                simp only [List.mem_map] at hz he'
                obtain ⟨y, hy, rfl⟩ := hz
                obtain ⟨x, hx, rfl⟩ := he'
                exact hconds (θ.f y, θ.f x) (by
                  simp only [List.mem_map, Rules.defPairs, List.mem_append, List.mem_flatMap]
                  exact ⟨(y, x), Or.inl ⟨y, hy, by simp [hx]⟩, rfl⟩))
              (Rules.nodup_map_of_laterPairs θ.f fun p hp heq => by
                have hp2 := (Rules.mem_laterPairs hp).2
                have hname : (θ.f p.2).IsName := (hθ p.2).2 (hwfD.dummies_name p.2 hp2)
                have hty : (θ.f p.2).ty.name = true := by
                  rw [Subst.ty_f_of_name hθ (hwfD.dummies_name p.2 hp2)]
                  exact hwfD.dummies_name p.2 hp2
                apply hconds (θ.f p.1, θ.f p.2) (by
                  simp only [List.mem_map, Rules.defPairs, List.mem_append]
                  exact ⟨p, Or.inr hp, rfl⟩)
                rw [heq]
                exact Consts.name_mem_self st.consts hname hty)
            unfold Translate.unfoldCert
            rwa [Def.inst_apply D hwfD θ] at h
      | fold d strict' =>
        obtain ⟨D, hD, rfl⟩ := hspec
        have hwfD : D.WF := hdefs D (List.mem_of_getElem? hD)
        simp only [Rules.foldRule, Language.apply_eq, Rules.defApp, Subst.apply_app, List.map_map,
          Function.comp_def, Subst.apply_var, List.map_cons, List.map_nil] at he hcs
        rw [he] at hT
        obtain ⟨rfl, rfl⟩ := Language.eq_inj hT
        cases cs with
        | nil => simp at hcs
        | cons c cs' =>
          cases cs' with
          | cons _ _ => simp at hcs
          | nil =>
            simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcs
            simp only [PTree.toC, hk, hD, PTree.toCList, List.headD_cons]
            have hconds := stepConds_hold hc
            simp only [stepConds, hA, Rules.foldRule] at hconds
            refine CValid.trans (e := θ.apply D.value)
              (ih c (by simp) (condsHold_of_mem hc (by simp)) _ _ _ _ hcs) (CValid.symm ?_)
            have h := CValid.unfold (db := db) (sig := L.sig) (c := st.consts) hD
              (List.forall₂_map_self D.args fun x _ => Subst.fitsTy_f hθ x)
              (List.forall₂_map_self D.dummies fun y hy =>
                ⟨(hθ y).2 (hwfD.dummies_name y hy), Subst.ty_f_of_name hθ (hwfD.dummies_name y hy)⟩)
              (fun z hz e' he' => by
                simp only [List.mem_map] at hz he'
                obtain ⟨y, hy, rfl⟩ := hz
                obtain ⟨x, hx, rfl⟩ := he'
                exact hconds (θ.f y, θ.f x) (by
                  simp only [List.mem_map, Rules.defPairs, List.mem_append, List.mem_flatMap]
                  exact ⟨(y, x), Or.inl ⟨y, hy, by simp [hx]⟩, rfl⟩))
              (Rules.nodup_map_of_laterPairs θ.f fun p hp heq => by
                have hp2 := (Rules.mem_laterPairs hp).2
                have hname : (θ.f p.2).IsName := (hθ p.2).2 (hwfD.dummies_name p.2 hp2)
                have hty : (θ.f p.2).ty.name = true := by
                  rw [Subst.ty_f_of_name hθ (hwfD.dummies_name p.2 hp2)]
                  exact hwfD.dummies_name p.2 hp2
                apply hconds (θ.f p.1, θ.f p.2) (by
                  simp only [List.mem_map, Rules.defPairs, List.mem_append]
                  exact ⟨p, Or.inr hp, rfl⟩)
                rw [heq]
                exact Consts.name_mem_self st.consts hname hty)
            unfold Translate.unfoldCert
            rwa [Def.inst_apply D hwfD θ] at h

end Cert


/-! ### The translation of a proof -/

theorem PTree.toDList_eq_map (L : Language) (db : Database) :
    ∀ cs : List PTree, PTree.toDList L db cs = cs.map (PTree.toD L db)
  | [] => rfl
  | t :: ts => by simp [PTree.toDList, PTree.toDList_eq_map L db ts]

theorem PTree.toCList_eq_map (L : Language) (db : Database) :
    ∀ cs : List PTree, PTree.toCList L db cs = cs.map (PTree.toC L db)
  | [] => rfl
  | t :: ts => by simp [PTree.toCList, PTree.toCList_eq_map L db ts]

theorem PTree.expr_toD (L : Language) (db : Database) : ∀ T : PTree, (T.toD L db).expr = T.expr
  | .hyp _ _ => rfl
  | .step e a θ cs => by
    simp only [PTree.toD, PTree.expr]
    split <;> rfl

theorem stepConds_sub (L : Language) (db : Database) (a : ℕ) (θ : Subst) :
    ∀ k ∈ stepConds db a θ, k ∈ stepConds (db.withConv L) a θ := by
  intro k hk
  by_cases h : a < db.asserts.length
  · rwa [Database.stepConds_withConv_lt L db h]
  · simp [stepConds, List.getElem?_eq_none (Nat.le_of_not_lt h)] at hk

mutual
/-- The conditions of the MM0 proof are among the tree's: those of the steps of the
file; a conversion adds none. -/
theorem PTree.conds_toD (L : Language) (db : Database) :
    ∀ T : PTree, ∀ k ∈ (T.toD L db).conds db, k ∈ T.conds (db.withConv L)
  | .hyp _ _, k, hk => by simp [PTree.toD, DTree.conds] at hk
  | .step e a θ cs, k, hk => by
    simp only [PTree.toD] at hk
    split at hk
    · simp only [DTree.conds, List.mem_append] at hk
      simp only [PTree.conds, List.mem_append]
      rcases hk with hk | hk
      · exact Or.inl (stepConds_sub L db a θ k hk)
      · exact Or.inr ((PTree.condsList_toDList L db cs).1 k hk)
    · simp only [DTree.conds] at hk
      simp only [PTree.conds, List.mem_append]
      rcases (PTree.condsList_toDList L db cs).2 (.hyp 0 e) k hk with h | h
      · exact Or.inr h
      · simp [DTree.conds] at h
    · simp [DTree.conds] at hk
theorem PTree.condsList_toDList (L : Language) (db : Database) : ∀ cs : List PTree,
    (∀ k ∈ DTree.condsList db (PTree.toDList L db cs), k ∈ PTree.condsList (db.withConv L) cs) ∧
    (∀ (d : DTree) (k : Cond), k ∈ ((PTree.toDList L db cs)[0]?.getD d).conds db →
      k ∈ PTree.condsList (db.withConv L) cs ∨ k ∈ d.conds db)
  | [] => ⟨fun k hk => by simp [PTree.toDList, DTree.condsList] at hk,
      fun d k hk => by simpa [PTree.toDList] using Or.inr hk⟩
  | t :: ts => by
    refine ⟨fun k hk => ?_, fun d k hk => ?_⟩
    · simp only [PTree.toDList, DTree.condsList, List.mem_append] at hk
      simp only [PTree.condsList, List.mem_append]
      rcases hk with hk | hk
      · exact Or.inl (PTree.conds_toD L db t k hk)
      · exact Or.inr ((PTree.condsList_toDList L db ts).1 k hk)
    · simp only [PTree.toDList, List.getElem?_cons_zero, Option.getD_some] at hk
      refine Or.inl ?_
      simp only [PTree.condsList, List.mem_append]
      exact Or.inl (PTree.conds_toD L db t k hk)
end

/-! ### The shape of the proof -/

section Proof

variable {L : Language} {db : Database} {st : Statement}

theorem sort_of_concl_eq {A : Assertion} {s : ℕ} {strict : Bool} {a b : Exp} (θ : Subst)
    (h : A.concl = L.eq s strict a b) : (θ.apply A.concl).ty.sort = L.judg := by
  rw [h, Language.apply_eq]; rfl

theorem child_sort {θ : Subst} (hθ : θ.Typed) {A : Assertion} (hA : ∀ h ∈ A.hyps, h.ty.sort ≠ L.judg)
    {cs : List PTree} (hcs : cs.map PTree.expr = A.hyps.map θ.apply) {c : PTree} (hc : c ∈ cs) :
    c.expr.ty.sort ≠ L.judg := by
  have : c.expr ∈ A.hyps.map θ.apply := by rw [← hcs]; exact List.mem_map_of_mem hc
  rw [List.mem_map] at this
  obtain ⟨h, hh, he⟩ := this
  rw [← he, Subst.sort_apply hθ]
  exact hA h hh

/-- A valid tree whose expression is no judgment stands for a valid MM0 proof: a step
of the file as it is, a `conv_s` step as a conversion with the certificate of its
second child. -/
theorem proof_valid (hL : L.WF db st) (hdefs : db.DefsWF) {T : PTree} (hs : Shape (db.withConv L) st T) :
    CondsHold (db.withConv L) st T → T.expr.ty.sort ≠ L.judg → DShape db L.sig st (T.toD L db) := by
  induction hs with
  | hyp h e hh he => intro _ _; exact DShape.hyp h e hh he
  | step e a θ cs A hA hθ hdom he hcs hall ih =>
    intro hc hsort
    simp only [PTree.expr] at hsort
    by_cases hlt : a < db.asserts.length
    · rw [Database.withConv_getElem?_lt L db hlt] at hA
      have hAmem := List.mem_of_getElem? hA
      simp only [PTree.toD, Database.ruleAt_of_lt L db hlt]
      refine DShape.step e a θ _ A hA hθ hdom he ?_ ?_
      · rw [PTree.toDList_eq_map, List.map_map, ← hcs]
        apply List.map_congr_left
        intro c _
        simp [PTree.expr_toD]
      · intro c' hc'
        rw [PTree.toDList_eq_map, List.mem_map] at hc'
        obtain ⟨c, hc'', rfl⟩ := hc'
        exact ih c hc'' (condsHold_of_mem hc hc'') (child_sort hθ (hL.assert_sort A hAmem).2 hcs hc'')
    · obtain ⟨k, hk, hmem⟩ := Database.ruleAt_of_getElem? L db hA (Nat.le_of_not_lt hlt)
      have hspec := Database.mem_all_spec L hmem
      cases k with
      | conv s' =>
        obtain ⟨rfl, hs'⟩ := hspec
        simp only [Rules.convRule, Rules.v, Subst.apply_var, List.map_cons, List.map_nil,
          Language.apply_eq] at he hcs
        cases cs with
        | nil => simp at hcs
        | cons cb cs' =>
          cases cs' with
          | nil => simp at hcs
          | cons ck cs'' =>
            cases cs'' with
            | cons _ _ => simp at hcs
            | nil =>
              simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcs
              obtain ⟨hcb, hck⟩ := hcs
              simp only [PTree.toD, hk, PTree.toCList, PTree.toDList, List.getElem?_cons_succ,
                List.getElem?_cons_zero, Option.getD_some]
              refine DShape.conv e _ _ ?_ ?_
              · rw [PTree.expr_toD, hcb, he]
                exact CValid.symm (cert_valid hL hdefs (hall ck (by simp)) (condsHold_of_mem hc (by simp))
                  s' true _ _ hck)
              · refine ih cb (by simp) (condsHold_of_mem hc (by simp)) ?_
                rw [hcb]
                have h1 : (θ.f ⟨1, ⟨s', false⟩⟩).ty.sort = s' := ((hθ ⟨1, ⟨s', false⟩⟩).1.1).symm
                have := hL.sorts_le
                omega
      | refl s' =>
        obtain ⟨rfl, _⟩ := hspec
        exact absurd (by rw [he]; exact sort_of_concl_eq θ rfl) hsort
      | cong t sa =>
        obtain ⟨rfl, _⟩ := hspec
        exact absurd (by rw [he]; exact sort_of_concl_eq θ rfl) hsort
      | unfold d strict' =>
        obtain ⟨D, hD, rfl⟩ := hspec
        exact absurd (by rw [he]; exact sort_of_concl_eq θ rfl) hsort
      | fold d strict' =>
        obtain ⟨D, hD, rfl⟩ := hspec
        exact absurd (by rw [he]; exact sort_of_concl_eq θ rfl) hsort

end Proof

/-! ### The extended database is well-formed -/

section WF

variable {L : Language}

theorem Exp.mem_varsList {v : Var} : ∀ es : List Exp, v ∈ Exp.varsList es ↔ ∃ e ∈ es, v ∈ e.vars
  | [] => by simp [Exp.varsList]
  | e :: es => by
    simp only [Exp.varsList, Finset.mem_union, Exp.mem_varsList es, List.mem_cons]
    aesop

theorem congVars_vars : ∀ (tys : List Ty) (k : ℕ),
    (∀ w ∈ (Rules.congVars tys k).2.1, w.vars ⊆ (Rules.congVars tys k).1.toFinset) ∧
    (∀ w ∈ (Rules.congVars tys k).2.2, w.vars ⊆ (Rules.congVars tys k).1.toFinset)
  | [], _ => by simp [Rules.congVars]
  | ty :: tys, k => by
    by_cases hn : ty.name = true
    · simp only [Rules.congVars, hn, ite_true, List.mem_cons, List.toFinset_cons]
      refine ⟨fun w hw => ?_, fun w hw => ?_⟩ <;> rcases hw with rfl | hw
      · simp [Rules.v, Exp.vars]
      · exact (congVars_vars tys (k + 1)).1 w hw |>.trans (Finset.subset_insert _ _)
      · simp [Rules.v, Exp.vars]
      · exact (congVars_vars tys (k + 1)).2 w hw |>.trans (Finset.subset_insert _ _)
    · simp only [Rules.congVars, hn, Bool.false_eq_true, ite_false, List.mem_cons, List.toFinset_cons]
      refine ⟨fun w hw => ?_, fun w hw => ?_⟩ <;> rcases hw with rfl | hw
      · simp [Rules.v, Exp.vars]
      · exact (congVars_vars tys (k + 2)).1 w hw |>.trans
          ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _))
      · simp [Rules.v, Exp.vars]
      · exact (congVars_vars tys (k + 2)).2 w hw |>.trans
          ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _))

theorem congHyps_vars (sa : Option ℕ) : ∀ (tys : List Ty) (as bs : List Exp) (i : ℕ),
    ∀ h ∈ Rules.congHyps L sa tys as bs i, ∀ v ∈ h.vars, ∃ w ∈ as ++ bs, v ∈ w.vars
  | ty :: tys, a :: as, b :: bs, i, h, hh, v, hv => by
    simp only [Rules.congHyps, List.mem_append] at hh
    rcases hh with hh | hh
    · split at hh
      · simp at hh
      · simp only [List.mem_singleton] at hh
        subst hh
        rw [Language.vars_eq, Finset.mem_union] at hv
        rcases hv with hv | hv
        · exact ⟨a, by simp, hv⟩
        · exact ⟨b, by simp, hv⟩
    · obtain ⟨w, hw, hvw⟩ := congHyps_vars sa tys as bs (i + 1) h hh v hv
      refine ⟨w, ?_, hvw⟩
      simp only [List.mem_append, List.mem_cons] at hw ⊢
      tauto
  | [], _, _, _, h, hh, _, _ => by simp [Rules.congHyps] at hh
  | _ :: _, [], _, _, h, hh, _, _ => by simp [Rules.congHyps] at hh
  | _ :: _, _ :: _, [], _, h, hh, _, _ => by simp [Rules.congHyps] at hh

theorem reflRule_WF (s : ℕ) : (Rules.reflRule L s).WF where
  concl_vars := by simp [Rules.reflRule, Language.vars_eq, Rules.v, Exp.vars]
  hyps_vars := by simp [Rules.reflRule]
  pairs_vars := by simp [Rules.reflRule]
  pairs_bound := by simp [Rules.reflRule]

theorem convRule_WF (s : ℕ) : (Rules.convRule L s).WF where
  concl_vars := by simp [Rules.convRule, Rules.v, Exp.vars]
  hyps_vars := by
    simp only [Rules.convRule, List.mem_cons, List.not_mem_nil, or_false]
    rintro h (rfl | rfl)
    · simp [Rules.v, Exp.vars]
    · simp [Language.vars_eq, Rules.v, Exp.vars]
  pairs_vars := by simp [Rules.convRule]
  pairs_bound := by simp [Rules.convRule]

theorem congRule_WF (t : ℕ) (sa : Option ℕ) : (Rules.congRule L t sa).WF where
  concl_vars := by
    simp only [Rules.congRule, Language.vars_eq, Exp.vars]
    intro v hv
    rw [Finset.mem_union, Exp.mem_varsList, Exp.mem_varsList] at hv
    rcases hv with ⟨w, hw, hvw⟩ | ⟨w, hw, hvw⟩
    · exact (congVars_vars _ 0).1 w hw hvw
    · exact (congVars_vars _ 0).2 w hw hvw
  hyps_vars := by
    simp only [Rules.congRule]
    intro h hh v hv
    obtain ⟨w, hw, hvw⟩ := congHyps_vars sa _ _ _ 0 h hh v hv
    rw [List.mem_append] at hw
    rcases hw with hw | hw
    · exact (congVars_vars _ 0).1 w hw hvw
    · exact (congVars_vars _ 0).2 w hw hvw
  pairs_vars := by simp [Rules.congRule]
  pairs_bound := by simp [Rules.congRule]

theorem mem_defPairs {D : Def} {p : Var × Var} (hp : p ∈ Rules.defPairs D) :
    p.1 ∈ D.dummies ∧ p.2 ∈ D.args ++ D.dummies := by
  simp only [Rules.defPairs, List.mem_append, List.mem_flatMap, List.mem_map] at hp
  rcases hp with ⟨y, hy, x, hx, rfl⟩ | hp
  · exact ⟨hy, by simp [hx]⟩
  · obtain ⟨h1, h2⟩ := Rules.mem_laterPairs hp
    exact ⟨h1, by simp [h2]⟩

theorem defApp_vars (D : Def) : (Rules.defApp D).vars = D.args.toFinset := by
  ext v
  simp only [Rules.defApp, Exp.vars, Exp.mem_varsList, List.mem_map, List.mem_toFinset]
  constructor
  · rintro ⟨e, ⟨x, hx, rfl⟩, hv⟩
    simp [Exp.vars] at hv
    exact hv ▸ hx
  · intro hv
    exact ⟨.var v, ⟨v, hv, rfl⟩, by simp [Exp.vars]⟩

theorem defRule_vars (D : Def) (hwf : D.WF) :
    (Rules.defApp D).vars ⊆ (D.args ++ D.dummies ++ [Rules.other D]).toFinset ∧
    D.value.vars ⊆ (D.args ++ D.dummies ++ [Rules.other D]).toFinset ∧
    (Exp.var (Rules.other D)).vars ⊆ (D.args ++ D.dummies ++ [Rules.other D]).toFinset := by
  refine ⟨?_, ?_, ?_⟩
  · rw [defApp_vars]
    intro v hv
    simp only [List.mem_toFinset, List.mem_append] at hv ⊢
    exact Or.inl (Or.inl hv)
  · intro v hv
    have := hwf.value_vars hv
    simp only [List.mem_toFinset, List.mem_append] at this ⊢
    exact Or.inl this
  · simp [Exp.vars]

theorem unfoldRule_WF (D : Def) (hwf : D.WF) (strict : Bool) : (Rules.unfoldRule L D strict).WF where
  concl_vars := by
    simp only [Rules.unfoldRule, Language.vars_eq]
    exact Finset.union_subset (defRule_vars D hwf).1 (defRule_vars D hwf).2.2
  hyps_vars := by
    simp only [Rules.unfoldRule, List.mem_singleton, forall_eq, Language.vars_eq]
    exact Finset.union_subset (defRule_vars D hwf).2.1 (defRule_vars D hwf).2.2
  pairs_vars := by
    simp only [Rules.unfoldRule]
    intro p hp
    obtain ⟨h1, h2⟩ := mem_defPairs hp
    simp only [List.mem_append, List.mem_singleton]
    exact ⟨Or.inl (Or.inr h1), Or.inl (List.mem_append.1 h2)⟩
  pairs_bound := by
    simp only [Rules.unfoldRule]
    intro p hp
    exact hwf.dummies_name p.1 (mem_defPairs hp).1

theorem foldRule_WF (D : Def) (hwf : D.WF) (strict : Bool) : (Rules.foldRule L D strict).WF where
  concl_vars := by
    simp only [Rules.foldRule, Language.vars_eq]
    exact Finset.union_subset (defRule_vars D hwf).2.2 (defRule_vars D hwf).1
  hyps_vars := by
    simp only [Rules.foldRule, List.mem_singleton, forall_eq, Language.vars_eq]
    exact Finset.union_subset (defRule_vars D hwf).2.2 (defRule_vars D hwf).2.1
  pairs_vars := by
    simp only [Rules.foldRule]
    intro p hp
    obtain ⟨h1, h2⟩ := mem_defPairs hp
    simp only [List.mem_append, List.mem_singleton]
    exact ⟨Or.inl (Or.inr h1), Or.inl (List.mem_append.1 h2)⟩
  pairs_bound := by
    simp only [Rules.foldRule]
    intro p hp
    exact hwf.dummies_name p.1 (mem_defPairs hp).1

/-- The extended database is well-formed when the file's assertions and definitions
are. -/
theorem Database.withConv_WF (db : Database) (hwf : db.WF) (hdefs : db.DefsWF) : (db.withConv L).WF := by
  intro A hA
  simp only [Database.withConv, List.mem_append, List.mem_map] at hA
  rcases hA with hA | ⟨⟨k, A'⟩, hmem, rfl⟩
  · exact hwf A hA
  · have hspec := Database.mem_all_spec L hmem
    cases k with
    | refl s => obtain ⟨rfl, _⟩ := hspec; exact reflRule_WF s
    | conv s => obtain ⟨rfl, _⟩ := hspec; exact convRule_WF s
    | cong t sa => obtain ⟨rfl, _⟩ := hspec; exact congRule_WF t sa
    | unfold d strict =>
      obtain ⟨D, hD, rfl⟩ := hspec
      exact unfoldRule_WF D (hdefs D (List.mem_of_getElem? hD)) strict
    | fold d strict =>
      obtain ⟨D, hD, rfl⟩ := hspec
      exact foldRule_WF D (hdefs D (List.mem_of_getElem? hD)) strict

end WF


/-! ### The variables of the proof -/

section Vars

variable {L : Language} {db : Database} {st : Statement}

theorem Exp.vars_of_mem_args {x : Exp} {f : ℕ} {t : Ty} {args : List Exp} (hx : x ∈ args) :
    x.vars ⊆ (Exp.app f t args).vars := by
  intro v hv
  simp only [Exp.vars]
  exact (Exp.mem_varsList args).2 ⟨x, hx, hv⟩

theorem PTree.mem_exprsList (db : Database) {x : Exp} :
    ∀ cs : List PTree, x ∈ PTree.exprsList db cs ↔ ∃ c ∈ cs, x ∈ c.exprs db
  | [] => by simp [PTree.exprsList]
  | c :: cs => by
    simp only [PTree.exprsList, List.mem_append, PTree.mem_exprsList db cs, List.mem_cons]
    aesop

theorem DTree.mem_exprsList (db : Database) {x : Exp} :
    ∀ cs : List DTree, x ∈ DTree.exprsList db cs ↔ ∃ c ∈ cs, x ∈ c.exprs db
  | [] => by simp [DTree.exprsList]
  | c :: cs => by
    simp only [DTree.exprsList, List.mem_append, DTree.mem_exprsList db cs, List.mem_cons]
    aesop

theorem CTree.mem_exprsList {x : Exp} :
    ∀ ks : List CTree, x ∈ CTree.exprsList ks ↔ ∃ k ∈ ks, x ∈ k.exprs
  | [] => by simp [CTree.exprsList]
  | k :: ks => by
    simp only [CTree.exprsList, List.mem_append, CTree.mem_exprsList ks, List.mem_cons]
    aesop

theorem PTree.vars_expr_sub (db : Database) (T : PTree) : T.expr.vars ⊆ T.allVars db := by
  intro v hv
  exact (PTree.mem_allVars db T v).2 ⟨T.expr, PTree.expr_mem_exprs db T, hv⟩

theorem PTree.allVars_child_sub (db : Database) {c : PTree} {e : Exp} {a : ℕ} {θ : Subst} {cs : List PTree}
    (hc : c ∈ cs) : c.allVars db ⊆ (PTree.step e a θ cs).allVars db := by
  intro v hv
  rw [PTree.mem_allVars] at hv ⊢
  obtain ⟨x, hx, hvx⟩ := hv
  refine ⟨x, ?_, hvx⟩
  simp only [PTree.exprs, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr ((PTree.mem_exprsList db cs).2 ⟨c, hc, hx⟩))

theorem congHyps_eq (sa : Option ℕ) : ∀ (tys : List Ty) (as bs : List Exp) (i : ℕ),
    ∀ h ∈ Rules.congHyps L sa tys as bs i, ∃ (s : ℕ) (strict : Bool) (a b : Exp), h = L.eq s strict a b
  | ty :: tys, a :: as, b :: bs, i, h, hh => by
    simp only [Rules.congHyps, List.mem_append] at hh
    rcases hh with hh | hh
    · split at hh
      · simp at hh
      · simp only [List.mem_singleton] at hh
        exact ⟨_, _, _, _, hh⟩
    · exact congHyps_eq sa tys as bs (i + 1) h hh
  | [], _, _, _, h, hh => by simp [Rules.congHyps] at hh
  | _ :: _, [], _, _, h, hh => by simp [Rules.congHyps] at hh
  | _ :: _, _ :: _, [], _, h, hh => by simp [Rules.congHyps] at hh

theorem mem_exprsList_congCerts (θ : Subst) : ∀ (tys : List Ty) (ks : List CTree) (k : ℕ) (x : Exp),
    x ∈ CTree.exprsList (Translate.congCerts θ tys ks k) →
    (∃ w ∈ (Rules.congVars tys k).2.1, x = θ.apply w) ∨ x ∈ CTree.exprsList ks
  | [], ks, k, x, hx => by simp [Translate.congCerts, CTree.exprsList] at hx
  | ty :: tys, ks, k, x, hx => by
    by_cases hn : ty.name = true
    · simp only [Translate.congCerts, hn, ite_true, CTree.exprsList, CTree.exprs, List.mem_append,
        List.mem_singleton] at hx
      rcases hx with rfl | hx
      · exact Or.inl ⟨Rules.v k ty, by simp [Rules.congVars, hn], by simp [Rules.v]⟩
      · rcases mem_exprsList_congCerts θ tys ks (k + 1) x hx with ⟨w, hw, hxw⟩ | hx
        · exact Or.inl ⟨w, by simp [Rules.congVars, hn, hw], hxw⟩
        · exact Or.inr hx
    · cases ks with
      | nil =>
        simp only [Translate.congCerts, hn, Bool.false_eq_true, ite_false, CTree.exprsList, CTree.exprs,
          List.mem_append, List.mem_singleton] at hx
        rcases hx with rfl | hx
        · exact Or.inl ⟨Rules.v k ty, by simp [Rules.congVars, hn], by simp [Rules.v]⟩
        · rcases mem_exprsList_congCerts θ tys [] (k + 2) x hx with ⟨w, hw, hxw⟩ | hx
          · exact Or.inl ⟨w, by simp [Rules.congVars, hn, hw], hxw⟩
          · exact Or.inr hx
      | cons k' ks' =>
        simp only [Translate.congCerts, hn, Bool.false_eq_true, ite_false, CTree.exprsList,
          List.mem_append] at hx
        rcases hx with hx | hx
        · exact Or.inr (by simp [CTree.exprsList, hx])
        · rcases mem_exprsList_congCerts θ tys ks' (k + 2) x hx with ⟨w, hw, hxw⟩ | hx
          · exact Or.inl ⟨w, by simp [Rules.congVars, hn, hw], hxw⟩
          · exact Or.inr (by simp [CTree.exprsList, hx])

/-- The variables of the certificate a rule tree stands for are among the tree's. -/
theorem cert_vars (hL : L.WF db st) (hdefs : db.DefsWF) {T : PTree} (hs : Shape (db.withConv L) st T) :
    ∀ (s : ℕ) (strict : Bool) (a b : Exp), T.expr = L.eq s strict a b →
      ∀ x ∈ (T.toC L db).exprs, x.vars ⊆ T.allVars (db.withConv L) := by
  induction hs with
  | hyp h e hh he =>
    intro s strict a b hT
    simp only [PTree.expr] at hT
    exfalso
    apply (hL.st_sort.2 st.hyps[h]! (by rw [getElem!_pos st.hyps h hh]; exact List.getElem_mem hh))
    rw [← he]
    exact sort_ne_of_eq hT
  | step e a θ cs A hA hθ hdom he hcs hall ih =>
    intro s strict a' b' hT
    simp only [PTree.expr] at hT
    have hroot : a'.vars ∪ b'.vars ⊆ (PTree.step e a θ cs).allVars (db.withConv L) := by
      rw [← Language.vars_eq, ← hT]; exact PTree.vars_expr_sub _ (.step e a θ cs)
    by_cases hlt : a < db.asserts.length
    · exfalso
      rw [Database.withConv_getElem?_lt L db hlt] at hA
      apply (hL.assert_sort A (List.mem_of_getElem? hA)).1
      rw [← Subst.sort_apply hθ A.concl, ← he]
      exact sort_ne_of_eq hT
    · obtain ⟨k, hk, hmem⟩ := Database.ruleAt_of_getElem? L db hA (Nat.le_of_not_lt hlt)
      have hspec := Database.mem_all_spec L hmem
      cases k with
      | refl s' =>
        obtain ⟨rfl, _⟩ := hspec
        simp only [Rules.reflRule, Language.apply_eq, Rules.v, Subst.apply_var] at he
        rw [he] at hT
        obtain ⟨rfl, rfl⟩ := Language.eq_inj hT
        simp only [PTree.toC, hk, CTree.exprs, List.mem_singleton]
        rintro x rfl
        exact Finset.subset_union_left.trans hroot
      | conv s' =>
        obtain ⟨rfl, hs'⟩ := hspec
        exfalso
        simp only [Rules.convRule, Rules.v, Subst.apply_var] at he
        have h1 : e.ty.sort = s' := by
          rw [he]
          exact ((hθ ⟨0, ⟨s', false⟩⟩).1.1).symm
        have h2 := sort_ne_of_eq hT
        have h3 := hL.sorts_le
        omega
      | cong t sa =>
        obtain ⟨rfl, _⟩ := hspec
        simp only [Rules.congRule, Language.apply_eq, Subst.apply_app] at he hcs
        rw [he] at hT
        obtain ⟨rfl, rfl⟩ := Language.eq_inj hT
        simp only [PTree.toC, hk, CTree.exprs]
        intro x hx
        rcases mem_exprsList_congCerts θ _ _ 0 x hx with ⟨w, hw, rfl⟩ | hx
        · exact (Exp.vars_of_mem_args (f := t) (t := ⟨L.sig.sort t, false⟩) (List.mem_map_of_mem hw)).trans
            (Finset.subset_union_left.trans hroot)
        · rw [PTree.toCList_eq_map, CTree.mem_exprsList] at hx
          obtain ⟨k', hk', hx⟩ := hx
          rw [List.mem_map] at hk'
          obtain ⟨c, hc, rfl⟩ := hk'
          have hcj : ∃ (s'' : ℕ) (strict'' : Bool) (a'' b'' : Exp), c.expr = L.eq s'' strict'' a'' b'' := by
            have : c.expr ∈ (Rules.congHyps L sa (L.sig.args t) (Rules.congVars (L.sig.args t) 0).2.1
                (Rules.congVars (L.sig.args t) 0).2.2 0).map θ.apply := by
              rw [← hcs]; exact List.mem_map_of_mem hc
            rw [List.mem_map] at this
            obtain ⟨h, hh, hce⟩ := this
            obtain ⟨s'', strict'', a'', b'', rfl⟩ := congHyps_eq sa _ _ _ 0 h hh
            exact ⟨s'', strict'', θ.apply a'', θ.apply b'', by rw [← hce, Language.apply_eq]⟩
          obtain ⟨s'', strict'', a'', b'', hc'⟩ := hcj
          exact (ih c hc s'' strict'' a'' b'' hc' x hx).trans (PTree.allVars_child_sub _ hc)
      | unfold d strict' =>
        obtain ⟨D, hD, rfl⟩ := hspec
        have hwfD : D.WF := hdefs D (List.mem_of_getElem? hD)
        simp only [Rules.unfoldRule, Language.apply_eq, Rules.defApp, Subst.apply_app, List.map_map,
          Function.comp_def, Subst.apply_var, List.map_cons, List.map_nil] at he hcs
        rw [he] at hT
        obtain ⟨rfl, rfl⟩ := Language.eq_inj hT
        cases cs with
        | nil => simp at hcs
        | cons c cs' =>
          cases cs' with
          | cons _ _ => simp at hcs
          | nil =>
            simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcs
            simp only [PTree.toC, hk, hD, PTree.toCList, List.headD_cons, CTree.exprs,
              Translate.unfoldCert, List.mem_append]
            intro x hx
            rcases hx with (hx | hx) | hx
            · exact (Exp.vars_of_mem_args (f := D.term) (t := D.ty) hx).trans
                (Finset.subset_union_left.trans hroot)
            · rw [List.mem_map] at hx
              obtain ⟨y, hy, rfl⟩ := hx
              have h1 : (θ.f y).vars ⊆ (θ.apply D.value).vars := by
                rw [Subst.vars_apply]
                exact Finset.subset_biUnion_of_mem (fun v => (θ.f v).vars) (hwfD.dummies_used y hy)
              have h2 : (θ.apply D.value).vars ⊆ c.expr.vars := by
                rw [hcs, Language.vars_eq]; exact Finset.subset_union_left
              exact h1.trans (h2.trans ((PTree.vars_expr_sub _ c).trans (PTree.allVars_child_sub _ (by simp))))
            · exact (ih c (by simp) _ _ _ _ hcs x hx).trans (PTree.allVars_child_sub _ (by simp))
      | fold d strict' =>
        obtain ⟨D, hD, rfl⟩ := hspec
        have hwfD : D.WF := hdefs D (List.mem_of_getElem? hD)
        simp only [Rules.foldRule, Language.apply_eq, Rules.defApp, Subst.apply_app, List.map_map,
          Function.comp_def, Subst.apply_var, List.map_cons, List.map_nil] at he hcs
        rw [he] at hT
        obtain ⟨rfl, rfl⟩ := Language.eq_inj hT
        cases cs with
        | nil => simp at hcs
        | cons c cs' =>
          cases cs' with
          | cons _ _ => simp at hcs
          | nil =>
            simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcs
            simp only [PTree.toC, hk, hD, PTree.toCList, List.headD_cons, CTree.exprs,
              Translate.unfoldCert, List.mem_append]
            intro x hx
            rcases hx with hx | (hx | hx)
            · exact (ih c (by simp) _ _ _ _ hcs x hx).trans (PTree.allVars_child_sub _ (by simp))
            · exact (Exp.vars_of_mem_args (f := D.term) (t := D.ty) hx).trans
                (Finset.subset_union_right.trans hroot)
            · rw [List.mem_map] at hx
              obtain ⟨y, hy, rfl⟩ := hx
              have h1 : (θ.f y).vars ⊆ (θ.apply D.value).vars := by
                rw [Subst.vars_apply]
                exact Finset.subset_biUnion_of_mem (fun v => (θ.f v).vars) (hwfD.dummies_used y hy)
              have h2 : (θ.apply D.value).vars ⊆ c.expr.vars := by
                rw [hcs, Language.vars_eq]; exact Finset.subset_union_right
              exact h1.trans (h2.trans ((PTree.vars_expr_sub _ c).trans (PTree.allVars_child_sub _ (by simp))))

/-- The variables of the MM0 proof are among the tree's. -/
theorem proof_vars (hL : L.WF db st) (hdefs : db.DefsWF) {T : PTree} (hs : Shape (db.withConv L) st T) :
    T.expr.ty.sort ≠ L.judg → ∀ v ∈ (T.toD L db).allVars db, v ∈ T.allVars (db.withConv L) := by
  induction hs with
  | hyp h e hh he =>
    intro _ v hv
    simpa [PTree.toD, DTree.allVars, PTree.allVars, DTree.exprs, PTree.exprs] using hv
  | step e a θ cs A hA hθ hdom he hcs hall ih =>
    intro hsort v hv
    simp only [PTree.expr] at hsort
    rw [DTree.mem_allVars] at hv
    obtain ⟨x, hx, hvx⟩ := hv
    rw [PTree.mem_allVars]
    by_cases hlt : a < db.asserts.length
    · rw [Database.withConv_getElem?_lt L db hlt] at hA
      have hAmem := List.mem_of_getElem? hA
      simp only [PTree.toD, Database.ruleAt_of_lt L db hlt, DTree.exprs, List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | hx | hx
      · exact ⟨x, by simp [PTree.exprs], hvx⟩
      · refine ⟨x, ?_, hvx⟩
        simp only [PTree.exprs, List.mem_cons, List.mem_append]
        rw [Database.stepConds_withConv_lt L db hlt]
        exact Or.inr (Or.inl hx)
      · rw [PTree.toDList_eq_map, DTree.mem_exprsList] at hx
        obtain ⟨c', hc', hx⟩ := hx
        rw [List.mem_map] at hc'
        obtain ⟨c, hc, rfl⟩ := hc'
        have := ih c hc (child_sort hθ (hL.assert_sort A hAmem).2 hcs hc) v ((DTree.mem_allVars db _ v).2 ⟨x, hx, hvx⟩)
        rw [PTree.mem_allVars] at this
        obtain ⟨x', hx', hvx'⟩ := this
        refine ⟨x', ?_, hvx'⟩
        simp only [PTree.exprs, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr ((PTree.mem_exprsList _ cs).2 ⟨c, hc, hx'⟩))
    · obtain ⟨k, hk, hmem⟩ := Database.ruleAt_of_getElem? L db hA (Nat.le_of_not_lt hlt)
      have hspec := Database.mem_all_spec L hmem
      cases k with
      | conv s' =>
        obtain ⟨rfl, hs'⟩ := hspec
        simp only [Rules.convRule, Rules.v, Subst.apply_var, List.map_cons, List.map_nil,
          Language.apply_eq] at he hcs
        cases cs with
        | nil => simp at hcs
        | cons cb cs' =>
          cases cs' with
          | nil => simp at hcs
          | cons ck cs'' =>
            cases cs'' with
            | cons _ _ => simp at hcs
            | nil =>
              simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcs
              obtain ⟨hcb, hck⟩ := hcs
              simp only [PTree.toD, hk, PTree.toCList, PTree.toDList, List.getElem?_cons_succ,
                List.getElem?_cons_zero, Option.getD_some, DTree.exprs, CTree.exprs, List.mem_cons,
                List.mem_append] at hx
              rcases hx with rfl | hx | hx
              · exact ⟨x, by simp [PTree.exprs], hvx⟩
              · have := cert_vars hL hdefs (hall ck (by simp)) s' true _ _ hck x hx hvx
                rw [PTree.mem_allVars] at this
                obtain ⟨x', hx', hvx'⟩ := this
                refine ⟨x', ?_, hvx'⟩
                simp only [PTree.exprs, List.mem_cons, List.mem_append]
                exact Or.inr (Or.inr ((PTree.mem_exprsList _ _).2 ⟨ck, by simp, hx'⟩))
              · have hsb : cb.expr.ty.sort ≠ L.judg := by
                  rw [hcb]
                  have h1 : (θ.f ⟨1, ⟨s', false⟩⟩).ty.sort = s' := ((hθ ⟨1, ⟨s', false⟩⟩).1.1).symm
                  have := hL.sorts_le
                  omega
                have := ih cb (by simp) hsb v ((DTree.mem_allVars db _ v).2 ⟨x, hx, hvx⟩)
                rw [PTree.mem_allVars] at this
                obtain ⟨x', hx', hvx'⟩ := this
                refine ⟨x', ?_, hvx'⟩
                simp only [PTree.exprs, List.mem_cons, List.mem_append]
                exact Or.inr (Or.inr ((PTree.mem_exprsList _ _).2 ⟨cb, by simp, hx'⟩))
      | refl s' =>
        obtain ⟨rfl, _⟩ := hspec
        exact absurd (by rw [he]; exact sort_of_concl_eq θ rfl) hsort
      | cong t sa =>
        obtain ⟨rfl, _⟩ := hspec
        exact absurd (by rw [he]; exact sort_of_concl_eq θ rfl) hsort
      | unfold d strict' =>
        obtain ⟨D, hD, rfl⟩ := hspec
        exact absurd (by rw [he]; exact sort_of_concl_eq θ rfl) hsort
      | fold d strict' =>
        obtain ⟨D, hD, rfl⟩ := hspec
        exact absurd (by rw [he]; exact sort_of_concl_eq θ rfl) hsort

end Vars

/-! ### The theorem -/

/-- A proof of the statement over the extended database stands for an MM0 proof of the
statement: the translation keeps validity, the conditions, the root and the
variables. -/
theorem toD_isProof {L : Language} {db : Database} {st : Statement} (hL : L.WF db st) (hdefs : db.DefsWF)
    {T : PTree} (h : IsProof (db.withConv L) st T) : IsProofD db L.sig st (T.toD L db) := by
  obtain ⟨⟨hs, hc⟩, he, hv⟩ := h
  have hsort : T.expr.ty.sort ≠ L.judg := by rw [he]; exact hL.st_sort.1
  refine ⟨⟨proof_valid hL hdefs hs hc hsort, ?_⟩, ?_, ?_⟩
  · intro k hk
    exact hc k (PTree.conds_toD L db T k hk)
  · rw [PTree.expr_toD, he]
  · intro v hv'
    exact hv v (proof_vars hL hdefs hs hsort v hv')

/-- The language fits an instance of the statement under a typed substitution. -/
theorem Language.WF.subst {L : Language} {db : Database} {st : Statement} (hL : L.WF db st) {σ : Subst}
    (hσ : σ.Typed) : L.WF db (st.subst σ) where
  sorts_le := hL.sorts_le
  assert_sort := hL.assert_sort
  st_sort := by
    refine ⟨?_, ?_⟩
    · simp only [Statement.subst]
      rw [Subst.sort_apply hσ]
      exact hL.st_sort.1
    · intro h hh
      simp only [Statement.subst, List.mem_map] at hh
      obtain ⟨h', hh', rfl⟩ := hh
      rw [Subst.sort_apply hσ]
      exact hL.st_sort.2 h' hh'

end Theory
