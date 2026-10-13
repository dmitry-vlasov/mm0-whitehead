/-
From an MM0 proof to a proof over the extended database (`docs/THEORY.md`,
"Definitions", milestone 10): a certificate becomes a rule tree, a conversion step a
`conv_s` step. Certificates are those of the `.mmb` format — without transitivity
(decision 14). The first part: substitutions from association lists, the index of a
rule in the extended database, and what a proof must fit.
-/
import Theory.ToD

namespace Theory

/-! ### Substitutions from association lists -/

namespace Subst

/-- What an association list gives a variable: the first entry for it, or itself. -/
def assoc (l : List (Var × Exp)) (v : Var) : Exp :=
  match l.find? (fun p => decide (p.1 = v)) with
  | some p => p.2
  | none => .var v

theorem assoc_of_not_mem (l : List (Var × Exp)) {v : Var} (hv : v ∉ l.map Prod.fst) : assoc l v = .var v := by
  unfold assoc
  have : l.find? (fun p => decide (p.1 = v)) = none := by
    rw [List.find?_eq_none]
    intro p hp h
    simp only [decide_eq_true_eq] at h
    exact hv (h ▸ List.mem_map_of_mem hp)
  rw [this]

/-- The substitution of an association list, the identity outside its keys. -/
def ofAssoc (l : List (Var × Exp)) : Subst :=
  Subst.ofFun (l.map Prod.fst).toFinset (assoc l) (fun v hv => assoc_of_not_mem l (by simpa using hv))

theorem ofAssoc_f (l : List (Var × Exp)) (v : Var) : (ofAssoc l).f v = assoc l v := rfl

theorem ofAssoc_dom (l : List (Var × Exp)) : (ofAssoc l).dom ⊆ (l.map Prod.fst).toFinset := by
  intro v hv
  simp only [ofAssoc, ofFun, Finset.mem_filter] at hv
  exact hv.1

/-- With distinct keys, an entry is what its key gets. -/
theorem assoc_of_mem : ∀ (l : List (Var × Exp)), (l.map Prod.fst).Nodup → ∀ {v : Var} {e : Exp}, (v, e) ∈ l → assoc l v = e
  | [], _, _, _, h => by simp at h
  | p :: l, hnd, v, e, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [List.mem_cons] at h
    unfold assoc
    rcases h with rfl | h
    · simp
    · have hne : p.1 ≠ v := fun heq => hnd.1 ⟨(v, e), h, heq.symm⟩
      rw [List.find?_cons_of_neg (by simpa using hne)]
      exact assoc_of_mem l hnd.2 h

theorem ofAssoc_f_of_mem {l : List (Var × Exp)} (hnd : (l.map Prod.fst).Nodup) {v : Var} {e : Exp} (h : (v, e) ∈ l) :
    (ofAssoc l).f v = e :=
  assoc_of_mem l hnd h

/-- Typed when every entry fits its key. -/
theorem ofAssoc_typed {l : List (Var × Exp)} (h : ∀ p ∈ l, FitsTy p.1.ty p.2) : (ofAssoc l).Typed := by
  intro v
  rw [ofAssoc_f]
  unfold assoc
  split
  · rename_i p hp
    have hmem := List.mem_of_find?_eq_some hp
    have hv : p.1 = v := by simpa using List.find?_some hp
    subst hv
    exact ⟨(h p hmem).1, (h p hmem).2⟩
  · exact ⟨Ty.fits_refl _, fun _ => trivial⟩

end Subst

/-! ### The index of a rule -/

namespace Rules

/-- The position of the first rule of a kind in a list, from `i`. -/
def indexOf (k : RuleKind) : List (RuleKind × Assertion) → ℕ → Option ℕ
  | [], _ => none
  | p :: l, i => if p.1 = k then some i else indexOf k l (i + 1)

theorem indexOf_spec (k : RuleKind) : ∀ (l : List (RuleKind × Assertion)) (i j : ℕ),
    indexOf k l i = some j → i ≤ j ∧ ∃ A, l[j - i]? = some (k, A)
  | [], _, _, h => by simp [indexOf] at h
  | p :: l, i, j, h => by
    simp only [indexOf] at h
    split at h
    · rename_i hp
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨le_rfl, p.2, ?_⟩
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq]
      rw [← hp]
    · obtain ⟨hij, A, hA⟩ := indexOf_spec k l (i + 1) j h
      refine ⟨by omega, A, ?_⟩
      rw [show j - i = (j - (i + 1)) + 1 by omega, List.getElem?_cons_succ]
      exact hA

theorem indexOf_isSome (k : RuleKind) : ∀ (l : List (RuleKind × Assertion)) (i : ℕ) {A : Assertion},
    (k, A) ∈ l → ∃ j, indexOf k l i = some j
  | [], _, _, h => by simp at h
  | p :: l, i, A, h => by
    simp only [indexOf]
    split
    · exact ⟨i, rfl⟩
    · rename_i hp
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact absurd rfl hp
      · exact indexOf_isSome k l (i + 1) h

end Rules

namespace Database

variable (L : Language) (db : Database)

/-- The index of a rule in the extended database. -/
def ruleIndex (k : RuleKind) : Option ℕ :=
  (Rules.indexOf k (Rules.all L db.defs) 0).map (· + db.asserts.length)

theorem ruleIndex_isSome {k : RuleKind} {A : Assertion} (h : (k, A) ∈ Rules.all L db.defs) :
    ∃ a, db.ruleIndex L k = some a := by
  obtain ⟨j, hj⟩ := Rules.indexOf_isSome k _ 0 h
  exact ⟨j + db.asserts.length, by simp [Database.ruleIndex, hj]⟩

/-- At the index of a rule stand that rule and an assertion of its shape. -/
theorem ruleIndex_spec {k : RuleKind} {a : ℕ} (h : db.ruleIndex L k = some a) :
    db.ruleAt L a = some k ∧ ∃ A, (db.withConv L).asserts[a]? = some A ∧ RuleSpec L db.defs k A := by
  simp only [Database.ruleIndex, Option.map_eq_some_iff] at h
  obtain ⟨j, hj, rfl⟩ := h
  obtain ⟨_, A, hA⟩ := Rules.indexOf_spec k _ 0 j hj
  simp only [Nat.sub_zero] at hA
  have hmem : (k, A) ∈ Rules.all L db.defs := List.mem_of_getElem? hA
  refine ⟨?_, A, ?_, mem_all_spec L hmem⟩
  · simp [Database.ruleAt, hA]
  · simp [Database.withConv, List.getElem?_append_right, hA]

end Database

/-! ### What a proof must fit -/

/-- A certificate of the `.mmb` format: no transitivity (decision 14). -/
def CTree.NoTrans : CTree → Prop
  | .refl _ => True
  | .symm k => k.NoTrans
  | .trans _ _ => False
  | .cong _ _ ks => ∀ k ∈ ks, k.NoTrans
  | .unfold _ _ _ => True

/-- The expressions a proof concludes at its nodes. -/
def DTree.nodeExprs : DTree → List Exp
  | .hyp _ e => [e]
  | .step e _ _ cs => e :: cs.flatMap DTree.nodeExprs
  | .conv e _ t => e :: t.nodeExprs

/-- Every certificate of a proof. -/
def DTree.certs : DTree → List CTree
  | .hyp _ _ => []
  | .step _ _ _ cs => cs.flatMap DTree.certs
  | .conv _ k t => k :: t.certs

mutual
/-- An expression over the language and the statement's constants: every sort is one
of the file's, a constant has its declared type, every application is of a term of
the file with its declared type, and the arguments fit the term's argument types. -/
def Language.Good (L : Language) (c : Consts) : Exp → Prop
  | .var v => v.ty.sort < L.sorts
  | .const k t => t = c.ty k ∧ t.sort < L.sorts
  | .app f t args => f < L.terms ∧ t = ⟨L.sig.sort f, false⟩ ∧ L.sig.sort f < L.sorts ∧ L.GoodArgs c (L.sig.args f) args
def Language.GoodArgs (L : Language) (c : Consts) : List Ty → List Exp → Prop
  | [], [] => True
  | ty :: tys, e :: es => FitsTy ty e ∧ ty.sort < L.sorts ∧ L.Good c e ∧ L.GoodArgs c tys es
  | _, _ => False
end

/-- A proof fits the language: every expression is over it, every conclusion has a
provable sort, and every certificate is of the `.mmb` format. -/
structure DTree.Fits (L : Language) (db : Database) (st : Statement) (D : DTree) : Prop where
  good : ∀ x ∈ D.exprs db, L.Good st.consts x
  provable : ∀ e ∈ D.nodeExprs, L.provable e.ty.sort = true
  noTrans : ∀ k ∈ D.certs, k.NoTrans

/-- A statement's bound variables depend on nothing: a name constant has no
declared dependencies, so the names that occur in it are itself alone. -/
def Consts.NameDeps (c : Consts) : Prop := ∀ k, (c.ty k).name = true → c.deps k = ∅


/-! ### The rule trees of a certificate -/

namespace Build

variable (L : Language) (db : Database)

/-- The `refl_s` tree for `a ≡ a`. -/
def reflTree (s : ℕ) (a : Exp) : PTree :=
  .step (L.eq s false a a) ((db.ruleIndex L (.refl s)).getD 0) (Subst.ofAssoc [(⟨0, ⟨s, false⟩⟩, a)]) []

/-- The substitution of a congruence step: the rule's variables, numbered as
`congVars` numbers them, given the arguments of the two sides. -/
def congAssoc : List Ty → List Exp → List Exp → ℕ → List (Var × Exp)
  | ty :: tys, e₁ :: es₁, e₂ :: es₂, k =>
    if ty.name then (⟨k, ty⟩, e₁) :: congAssoc tys es₁ es₂ (k + 1)
    else (⟨k, ty⟩, e₁) :: (⟨k + 1, ty⟩, e₂) :: congAssoc tys es₁ es₂ (k + 2)
  | _, _, _, _ => []

/-- The first position at which two lists differ. -/
def firstDiff : List Exp → List Exp → ℕ → Option ℕ
  | e₁ :: es₁, e₂ :: es₂, i => if e₁ = e₂ then firstDiff es₁ es₂ (i + 1) else some i
  | _, _, _ => none

/-- The substitution of an unfolding or folding step: the arguments, the dummies, and
the other side. -/
def unfoldAssoc (D : Def) (es zs : List Exp) (b : Exp) : List (Var × Exp) :=
  D.args.zip es ++ D.dummies.zip zs ++ [(Rules.other D, b)]

end Build

open Build in
mutual
/-- The rule tree for `a ≡ b` from a certificate converting `a` to `b` (`strict`: for
`a ≡' b`, which asks `a ≠ b`): `refl_s` for reflexivity; the reverse for symmetry; a
congruence step with the children of the arguments that do not take names, strict at
the first argument where the sides differ; `unfold_f` with a reflexive child for an
unfolding. Transitivity, which the `.mmb` format has not (decision 14), is given
reflexivity. -/
def CTree.toTree (L : Language) (db : Database) (strict : Bool) (s : ℕ) : CTree → Exp → Exp → PTree
  | .refl _, a, _ => reflTree L db s a
  | .symm k, a, b => CTree.toTreeR L db strict s k b a
  | .trans _ _, a, _ => reflTree L db s a
  | .cong f _ ks, a, b =>
    match a, b with
    | .app _ _ es₁, .app _ _ es₂ =>
      if es₁ = es₂ then reflTree L db s a
      else
        let pick := if strict then firstDiff es₁ es₂ 0 else none
        .step (L.eq s strict a b) ((db.ruleIndex L (.cong f pick)).getD 0)
          (Subst.ofAssoc (congAssoc (L.sig.args f) es₁ es₂ 0))
          (CTree.toTreeList L db pick (L.sig.args f) ks es₁ es₂ 0)
    | _, _ => reflTree L db s a
  | .unfold d es zs, a, b =>
    match db.defs[d]? with
    | some D =>
      .step (L.eq s strict a b) ((db.ruleIndex L (.unfold d strict)).getD 0)
        (Subst.ofAssoc (unfoldAssoc D es zs b)) [reflTree L db s b]
    | none => reflTree L db s a
/-- The rule tree for `b ≡ a` from a certificate converting `a` to `b`: as `toTree`
with the sides exchanged, `fold_f` for an unfolding. -/
def CTree.toTreeR (L : Language) (db : Database) (strict : Bool) (s : ℕ) : CTree → Exp → Exp → PTree
  | .refl _, a, _ => reflTree L db s a
  | .symm k, a, b => CTree.toTree L db strict s k b a
  | .trans _ _, a, _ => reflTree L db s a
  | .cong f _ ks, a, b =>
    match a, b with
    | .app _ _ es₁, .app _ _ es₂ =>
      if es₁ = es₂ then reflTree L db s a
      else
        let pick := if strict then firstDiff es₂ es₁ 0 else none
        .step (L.eq s strict b a) ((db.ruleIndex L (.cong f pick)).getD 0)
          (Subst.ofAssoc (congAssoc (L.sig.args f) es₂ es₁ 0))
          (CTree.toTreeListR L db pick (L.sig.args f) ks es₁ es₂ 0)
    | _, _ => reflTree L db s a
  | .unfold d es zs, a, b =>
    match db.defs[d]? with
    | some D =>
      .step (L.eq s strict b a) ((db.ruleIndex L (.fold d strict)).getD 0)
        (Subst.ofAssoc (unfoldAssoc D es zs b)) [reflTree L db s b]
    | none => reflTree L db s b
/-- The children of a congruence step: at every argument that does not take names,
the tree of its certificate, strict at `pick`. -/
def CTree.toTreeList (L : Language) (db : Database) (pick : Option ℕ) :
    List Ty → List CTree → List Exp → List Exp → ℕ → List PTree
  | ty :: tys, k :: ks, e₁ :: es₁, e₂ :: es₂, i =>
    (if ty.name then [] else [CTree.toTree L db (pick == some i) ty.sort k e₁ e₂]) ++
      CTree.toTreeList L db pick tys ks es₁ es₂ (i + 1)
  | _, _, _, _, _ => []
/-- The same with the sides exchanged. -/
def CTree.toTreeListR (L : Language) (db : Database) (pick : Option ℕ) :
    List Ty → List CTree → List Exp → List Exp → ℕ → List PTree
  | ty :: tys, k :: ks, e₁ :: es₁, e₂ :: es₂, i =>
    (if ty.name then [] else [CTree.toTreeR L db (pick == some i) ty.sort k e₁ e₂]) ++
      CTree.toTreeListR L db pick tys ks es₁ es₂ (i + 1)
  | _, _, _, _, _ => []
end

mutual
/-- The proof over the extended database an MM0 proof stands for: a step as it is; a
conversion that converts an expression to itself dropped; any other as a `conv_s` step
over the proof of the converted expression and the strict rule tree of the
certificate, backwards. -/
def DTree.toP (L : Language) (db : Database) : DTree → PTree
  | .hyp h e => .hyp h e
  | .step e a θ cs => .step e a θ (DTree.toPList L db cs)
  | .conv e k t =>
    if e = t.expr then DTree.toP L db t
    else
      .step e ((db.ruleIndex L (.conv e.ty.sort)).getD 0)
        (Subst.ofAssoc [(⟨0, ⟨e.ty.sort, false⟩⟩, e), (⟨1, ⟨e.ty.sort, false⟩⟩, t.expr)])
        [DTree.toP L db t, CTree.toTreeR L db true e.ty.sort k t.expr e]
def DTree.toPList (L : Language) (db : Database) : List DTree → List PTree
  | [] => []
  | t :: ts => DTree.toP L db t :: DTree.toPList L db ts
end


/-! ### Lemmas for the validity of the built trees -/

section Lemmas

variable {L : Language} {db : Database} {st : Statement}

theorem Language.good_sort {c : Consts} {e : Exp} (h : L.Good c e) : e.ty.sort < L.sorts := by
  cases e with
  | var v => exact h
  | const k t => exact h.2
  | app f t args => obtain ⟨_, rfl, h, _⟩ := h; exact h

/-- The expressions of a list of good arguments, by position. -/
theorem Language.goodArgs_spec {c : Consts} : ∀ (tys : List Ty) (es : List Exp), L.GoodArgs c tys es →
    tys.length = es.length ∧ ∀ (i : ℕ) (ty : Ty) (e : Exp), tys[i]? = some ty → es[i]? = some e →
      FitsTy ty e ∧ ty.sort < L.sorts ∧ L.Good c e
  | [], [], _ => ⟨rfl, fun i _ _ h => by simp at h⟩
  | ty :: tys, e :: es, h => by
    obtain ⟨h1, h2, h3, h4⟩ := h
    obtain ⟨hl, hi⟩ := Language.goodArgs_spec tys es h4
    refine ⟨by simp [hl], ?_⟩
    intro i ty' e' hty he
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hty he
      subst hty; subst he
      exact ⟨h1, h2, h3⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hty he
      exact hi i ty' e' hty he
  | [], _ :: _, h => by simp [Language.GoodArgs] at h
  | _ :: _, [], h => by simp [Language.GoodArgs] at h

/-- The names in a name of a name type are itself alone, when the bound variables of
the statement depend on nothing and the name has its declared type. -/
theorem Consts.names_of_name {c : Consts} (hnd : c.NameDeps) {e : Exp} (hn : e.IsName) (ht : e.ty.name = true)
    (hc : ∀ k t, e = Exp.const k t → t = c.ty k) : ∀ x, x ∈ c.names e ↔ x = e := by
  intro x
  rw [Consts.mem_names]
  cases e with
  | var v =>
    simp only [Exp.vars, Finset.mem_singleton, Exp.consts, Finset.notMem_empty, false_and, exists_false,
      or_false, exists_eq_left]
    simp only [Exp.ty] at ht
    constructor
    · rintro ⟨_, rfl⟩; rfl
    · rintro rfl; exact ⟨ht, rfl⟩
  | const k t =>
    simp only [Exp.vars, Finset.notMem_empty, false_and, exists_false, Exp.consts, Finset.mem_singleton,
      exists_eq_left, false_or]
    simp only [Exp.ty] at ht
    have hdeps : c.deps k = ∅ := hnd k (by rw [← hc k t rfl]; exact ht)
    simp [hdeps, ht]
  | app _ _ _ => exact absurd hn (by simp [Exp.IsName])

/-! The congruence substitution. -/

theorem congAssoc_keys : ∀ (tys : List Ty) (es₁ es₂ : List Exp) (k : ℕ),
    tys.length = es₁.length → tys.length = es₂.length →
    (Build.congAssoc tys es₁ es₂ k).map Prod.fst = (Rules.congVars tys k).1
  | [], [], [], _, _, _ => rfl
  | ty :: tys, e₁ :: es₁, e₂ :: es₂, k, h1, h2 => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
    by_cases hn : ty.name = true
    · simp [Build.congAssoc, Rules.congVars, hn, congAssoc_keys tys es₁ es₂ (k + 1) h1 h2]
    · simp [Build.congAssoc, Rules.congVars, hn, congAssoc_keys tys es₁ es₂ (k + 2) h1 h2]
  | [], _ :: _, _, _, h1, _ => by simp at h1
  | _ :: _, [], _, _, h1, _ => by simp at h1
  | [], [], _ :: _, _, _, h2 => by simp at h2
  | _ :: _, _ :: _, [], _, _, h2 => by simp at h2

theorem congAssoc_keys_ge : ∀ (tys : List Ty) (es₁ es₂ : List Exp) (k : ℕ),
    ∀ p ∈ Build.congAssoc tys es₁ es₂ k, k ≤ p.1.id
  | ty :: tys, e₁ :: es₁, e₂ :: es₂, k, p, hp => by
    by_cases hn : ty.name = true
    · simp only [Build.congAssoc, hn, if_true, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact le_rfl
      · exact (Nat.le_succ k).trans (congAssoc_keys_ge tys es₁ es₂ (k + 1) p hp)
    · simp only [Build.congAssoc, hn, Bool.false_eq_true, if_false, List.mem_cons] at hp
      rcases hp with rfl | rfl | hp
      · exact le_rfl
      · exact Nat.le_succ k
      · exact (by omega : k ≤ k + 2).trans (congAssoc_keys_ge tys es₁ es₂ (k + 2) p hp)
  | [], _, _, _, p, hp => by simp [Build.congAssoc] at hp
  | _ :: _, [], _, _, p, hp => by simp [Build.congAssoc] at hp
  | _ :: _, _ :: _, [], _, p, hp => by simp [Build.congAssoc] at hp

theorem congAssoc_nodup : ∀ (tys : List Ty) (es₁ es₂ : List Exp) (k : ℕ),
    ((Build.congAssoc tys es₁ es₂ k).map Prod.fst).Nodup
  | ty :: tys, e₁ :: es₁, e₂ :: es₂, k => by
    by_cases hn : ty.name = true
    · simp only [Build.congAssoc, hn, if_true, List.map_cons, List.nodup_cons, List.mem_map]
      refine ⟨?_, congAssoc_nodup tys es₁ es₂ (k + 1)⟩
      rintro ⟨p, hp, hpk⟩
      have := congAssoc_keys_ge tys es₁ es₂ (k + 1) p hp
      rw [hpk] at this
      simp only [] at this
      omega
    · simp only [Build.congAssoc, hn, Bool.false_eq_true, if_false, List.map_cons, List.nodup_cons,
        List.mem_cons, List.mem_map]
      refine ⟨?_, ?_, congAssoc_nodup tys es₁ es₂ (k + 2)⟩
      · rintro (h | ⟨p, hp, hpk⟩)
        · simp at h
        · have := congAssoc_keys_ge tys es₁ es₂ (k + 2) p hp
          rw [hpk] at this
          simp only [] at this
          omega
      · rintro ⟨p, hp, hpk⟩
        have := congAssoc_keys_ge tys es₁ es₂ (k + 2) p hp
        rw [hpk] at this
        simp only [] at this
        omega
  | [], _, _, _ => by simp [Build.congAssoc]
  | _ :: _, [], _, _ => by simp [Build.congAssoc]
  | _ :: _, _ :: _, [], _ => by simp [Build.congAssoc]

theorem congAssoc_fits {c : Consts} : ∀ (tys : List Ty) (es₁ es₂ : List Exp) (k : ℕ),
    L.GoodArgs c tys es₁ → L.GoodArgs c tys es₂ → ∀ p ∈ Build.congAssoc tys es₁ es₂ k, FitsTy p.1.ty p.2
  | ty :: tys, e₁ :: es₁, e₂ :: es₂, k, h1, h2, p, hp => by
    obtain ⟨f1, _, _, g1⟩ := h1
    obtain ⟨f2, _, _, g2⟩ := h2
    by_cases hn : ty.name = true
    · simp only [Build.congAssoc, hn, if_true, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact f1
      · exact congAssoc_fits tys es₁ es₂ (k + 1) g1 g2 p hp
    · simp only [Build.congAssoc, hn, Bool.false_eq_true, if_false, List.mem_cons] at hp
      rcases hp with rfl | rfl | hp
      · exact f1
      · exact f2
      · exact congAssoc_fits tys es₁ es₂ (k + 2) g1 g2 p hp
  | [], _, _, _, _, _, p, hp => by simp [Build.congAssoc] at hp
  | _ :: _, [], _, _, _, _, p, hp => by simp [Build.congAssoc] at hp
  | _ :: _, _ :: _, [], _, _, _, p, hp => by simp [Build.congAssoc] at hp

/-- The rule's variables under a substitution that agrees with the assignment are the
two sides. -/
theorem congVars_apply : ∀ (tys : List Ty) (es₁ es₂ : List Exp) (k : ℕ) (θ : Subst),
    tys.length = es₁.length → tys.length = es₂.length →
    (∀ (i : ℕ) (u : Ty), tys[i]? = some u → u.name = true → es₁[i]? = es₂[i]?) →
    (∀ p ∈ Build.congAssoc tys es₁ es₂ k, θ.f p.1 = p.2) →
    (Rules.congVars tys k).2.1.map θ.apply = es₁ ∧ (Rules.congVars tys k).2.2.map θ.apply = es₂
  | [], [], [], _, _, _, _, _, _ => by simp [Rules.congVars]
  | ty :: tys, e₁ :: es₁, e₂ :: es₂, k, θ, h1, h2, hnames, hθ => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
    have hnames' : ∀ (i : ℕ) (u : Ty), tys[i]? = some u → u.name = true → es₁[i]? = es₂[i]? :=
      fun i u hu hn => by simpa using hnames (i + 1) u (by simpa using hu) hn
    by_cases hn : ty.name = true
    · have he : e₁ = e₂ := by simpa using hnames 0 ty (by simp) hn
      simp only [Build.congAssoc, hn, if_true, List.mem_cons, forall_eq_or_imp] at hθ
      obtain ⟨ih1, ih2⟩ := congVars_apply tys es₁ es₂ (k + 1) θ h1 h2 hnames' hθ.2
      simp [Rules.congVars, hn, Rules.v, Subst.apply_var, hθ.1, ih1, ih2, he]
    · simp only [Build.congAssoc, hn, Bool.false_eq_true, if_false, List.mem_cons, forall_eq_or_imp] at hθ
      obtain ⟨ih1, ih2⟩ := congVars_apply tys es₁ es₂ (k + 2) θ h1 h2 hnames' hθ.2.2
      simp [Rules.congVars, hn, Rules.v, Subst.apply_var, hθ.1, hθ.2.1, ih1, ih2]
  | [], _ :: _, _, _, _, h1, _, _, _ => by simp at h1
  | _ :: _, [], _, _, _, h1, _, _, _ => by simp at h1
  | [], [], _ :: _, _, _, _, h2, _, _ => by simp at h2
  | _ :: _, _ :: _, [], _, _, _, h2, _, _ => by simp at h2

/-! The first differing position. -/

theorem firstDiff_spec : ∀ (es₁ es₂ : List Exp) (i j : ℕ), Build.firstDiff es₁ es₂ i = some j →
    i ≤ j ∧ es₁[j - i]? ≠ es₂[j - i]?
  | e₁ :: es₁, e₂ :: es₂, i, j, h => by
    simp only [Build.firstDiff] at h
    split at h
    · obtain ⟨hij, hne⟩ := firstDiff_spec es₁ es₂ (i + 1) j h
      refine ⟨by omega, ?_⟩
      rw [show j - i = (j - (i + 1)) + 1 by omega]
      simpa using hne
    · simp only [Option.some.injEq] at h
      subst h
      refine ⟨le_rfl, ?_⟩
      simp only [Nat.sub_self, List.getElem?_cons_zero, ne_eq, Option.some.injEq]
      assumption
  | [], _, _, _, h => by simp [Build.firstDiff] at h
  | _ :: _, [], _, _, h => by simp [Build.firstDiff] at h

theorem firstDiff_some : ∀ (es₁ es₂ : List Exp) (i : ℕ), es₁ ≠ es₂ → es₁.length = es₂.length →
    ∃ j, Build.firstDiff es₁ es₂ i = some j
  | e₁ :: es₁, e₂ :: es₂, i, hne, hl => by
    simp only [Build.firstDiff]
    by_cases he : e₁ = e₂
    · subst he
      simp only [if_true]
      exact firstDiff_some es₁ es₂ (i + 1) (fun h => hne (by rw [h])) (by simpa using hl)
    · exact ⟨i, by simp [he]⟩
  | [], [], _, hne, _ => absurd rfl hne
  | [], _ :: _, _, _, hl => by simp at hl
  | _ :: _, [], _, _, hl => by simp at hl

/-! Each rule is in the list. -/

theorem mem_all_refl {s : ℕ} (hs : s < L.sorts) (defs : List Def) :
    (RuleKind.refl s, Rules.reflRule L s) ∈ Rules.all L defs := by
  simp only [Rules.all, List.mem_append, Rules.sortRules, List.mem_flatMap, List.mem_range]
  exact Or.inl (Or.inl ⟨s, hs, by simp⟩)

theorem mem_all_conv {s : ℕ} (hs : s < L.sorts) (hp : L.provable s = true) (defs : List Def) :
    (RuleKind.conv s, Rules.convRule L s) ∈ Rules.all L defs := by
  simp only [Rules.all, List.mem_append, Rules.sortRules, List.mem_flatMap, List.mem_range]
  exact Or.inl (Or.inl ⟨s, hs, by simp [hp]⟩)

theorem mem_regularArgs {tys : List Ty} {i : ℕ} {u : Ty} (hu : tys[i]? = some u) (hn : u.name = false) :
    i ∈ Rules.regularArgs tys := by
  have hi : i < tys.length := (List.getElem?_eq_some_iff.1 hu).1
  simp only [Rules.regularArgs, List.mem_filter, List.mem_range, Bool.not_eq_eq_eq_not, Bool.not_true]
  refine ⟨hi, ?_⟩
  rw [getElem!_pos tys i hi]
  have := List.getElem?_eq_some_iff.1 hu
  obtain ⟨_, h⟩ := this
  rw [h]
  exact hn

theorem mem_all_cong {t : ℕ} (ht : t < L.terms) {pick : Option ℕ}
    (hreg : ¬(Rules.regularArgs (L.sig.args t)).isEmpty = true)
    (hpick : ∀ i, pick = some i → i ∈ Rules.regularArgs (L.sig.args t)) (defs : List Def) :
    (RuleKind.cong t pick, Rules.congRule L t pick) ∈ Rules.all L defs := by
  simp only [Rules.all, List.mem_append, Rules.termRules, List.mem_flatMap, List.mem_range]
  refine Or.inl (Or.inr ⟨t, ht, ?_⟩)
  rw [if_neg hreg]
  cases pick with
  | none => simp
  | some i =>
    simp only [List.mem_cons, List.mem_map, Prod.mk.injEq]
    exact Or.inr ⟨i, hpick i rfl, rfl, rfl⟩

theorem mem_all_unfold {defs : List Def} {d : ℕ} {D : Def} (hD : defs[d]? = some D) (strict : Bool) :
    (RuleKind.unfold d strict, Rules.unfoldRule L D strict) ∈ Rules.all L defs := by
  simp only [Rules.all, List.mem_append, Rules.defRules, List.mem_flatMap]
  refine Or.inr ⟨(D, d), ?_, ?_⟩
  · exact List.mem_of_getElem? (by rw [List.getElem?_zipIdx, hD]; simp)
  · cases strict <;> simp

theorem mem_all_fold {defs : List Def} {d : ℕ} {D : Def} (hD : defs[d]? = some D) (strict : Bool) :
    (RuleKind.fold d strict, Rules.foldRule L D strict) ∈ Rules.all L defs := by
  simp only [Rules.all, List.mem_append, Rules.defRules, List.mem_flatMap]
  refine Or.inr ⟨(D, d), ?_, ?_⟩
  · exact List.mem_of_getElem? (by rw [List.getElem?_zipIdx, hD]; simp)
  · cases strict <;> simp

/-- The rule of a kind, at its index: its assertion by `RuleSpec`. -/
theorem rule_at_index {k : RuleKind} {A : Assertion} (h : (k, A) ∈ Rules.all L db.defs) :
    ∃ a, db.ruleIndex L k = some a ∧ db.ruleAt L a = some k ∧
      ∃ A', (db.withConv L).asserts[a]? = some A' ∧ Database.RuleSpec L db.defs k A' := by
  obtain ⟨a, ha⟩ := Database.ruleIndex_isSome L db h
  obtain ⟨h1, A', h2, h3⟩ := Database.ruleIndex_spec L db ha
  exact ⟨a, ha, h1, A', h2, h3⟩

/-! The reflexivity tree. -/

/-- The variables of a list of expressions. -/
def Exp.varsOf (es : List Exp) : Finset Var := es.foldr (fun e s => e.vars ∪ s) ∅

theorem Exp.mem_varsOf {v : Var} : ∀ es : List Exp, v ∈ Exp.varsOf es ↔ ∃ e ∈ es, v ∈ e.vars
  | [] => by simp [Exp.varsOf]
  | e :: es => by
    show v ∈ e.vars ∪ Exp.varsOf es ↔ _
    simp [Exp.mem_varsOf es]

/-- The variables of a tree with a step at the root: of its expression, of the
conditions of the step, and of the children. -/
theorem PTree.mem_allVars_step (db : Database) {v : Var} {e : Exp} {a : ℕ} {θ : Subst} {cs : List PTree} :
    v ∈ (PTree.step e a θ cs).allVars db ↔
      v ∈ e.vars ∨ (∃ k ∈ stepConds db a θ, v ∈ k.1.vars ∨ v ∈ k.2.vars) ∨ ∃ c ∈ cs, v ∈ c.allVars db := by
  rw [PTree.mem_allVars]
  simp only [PTree.exprs, List.mem_cons, List.mem_append, List.mem_flatMap, PTree.mem_exprsList]
  constructor
  · rintro ⟨x, (rfl | ⟨k, hk, hx⟩ | ⟨c, hc, hx⟩), hv⟩
    · exact Or.inl hv
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inl ⟨k, hk, Or.inl hv⟩)
      · exact Or.inr (Or.inl ⟨k, hk, Or.inr hv⟩)
    · exact Or.inr (Or.inr ⟨c, hc, (PTree.mem_allVars db c v).2 ⟨x, hx, hv⟩⟩)
  · rintro (hv | ⟨k, hk, hv | hv⟩ | ⟨c, hc, hv⟩)
    · exact ⟨e, Or.inl rfl, hv⟩
    · exact ⟨k.1, Or.inr (Or.inl ⟨k, hk, by simp⟩), hv⟩
    · exact ⟨k.2, Or.inr (Or.inl ⟨k, hk, by simp⟩), hv⟩
    · obtain ⟨x, hx, hv⟩ := (PTree.mem_allVars db c v).1 hv
      exact ⟨x, Or.inr (Or.inr ⟨c, hc, hx⟩), hv⟩

theorem reflTree_valid {s : ℕ} (hs : s < L.sorts) {a : Exp} (hsa : a.ty.sort = s) :
    Shape (db.withConv L) st (Build.reflTree L db s a) ∧ CondsHold (db.withConv L) st (Build.reflTree L db s a) ∧
      (Build.reflTree L db s a).expr = L.eq s false a a ∧
      ∀ v ∈ (Build.reflTree L db s a).allVars (db.withConv L), v ∈ a.vars := by
  obtain ⟨idx, hidx, _, A, hA, hspec⟩ := rule_at_index (db := db) (mem_all_refl hs db.defs)
  obtain ⟨rfl, _⟩ := hspec
  have hθ : (Subst.ofAssoc [(⟨0, ⟨s, false⟩⟩, a)]).f ⟨0, ⟨s, false⟩⟩ = a :=
    Subst.ofAssoc_f_of_mem (by simp) (by simp)
  have hsc : stepConds (db.withConv L) ((db.ruleIndex L (.refl s)).getD 0) (Subst.ofAssoc [(⟨0, ⟨s, false⟩⟩, a)]) = [] := by
    rw [hidx, Option.getD_some]
    unfold stepConds
    rw [hA]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Build.reflTree, hidx, Option.getD_some]
    refine Shape.step _ _ _ _ _ hA ?_ ?_ ?_ rfl (fun _ h => by simp at h)
    · exact Subst.ofAssoc_typed (by
        simp only [List.mem_singleton, forall_eq, FitsTy]
        exact ⟨⟨hsa.symm, fun h => by simp at h⟩, fun h => by simp at h⟩)
    · exact (Subst.ofAssoc_dom _).trans (by simp [Rules.reflRule])
    · simp [Rules.reflRule, Language.apply_eq, Rules.v, Subst.apply_var, hθ]
  · intro k hk
    have hk' : k ∈ stepConds (db.withConv L) ((db.ruleIndex L (.refl s)).getD 0) (Subst.ofAssoc [(⟨0, ⟨s, false⟩⟩, a)]) ++
        PTree.condsList (db.withConv L) [] := hk
    rw [hsc] at hk'
    simp [PTree.condsList] at hk'
  · simp [Build.reflTree, PTree.expr]
  · intro v hv
    have hv' : v ∈ (PTree.step (L.eq s false a a) ((db.ruleIndex L (.refl s)).getD 0)
        (Subst.ofAssoc [(⟨0, ⟨s, false⟩⟩, a)]) []).allVars (db.withConv L) := hv
    rw [PTree.mem_allVars_step, hsc] at hv'
    rcases hv' with hv' | ⟨_, h, _⟩ | ⟨_, h, _⟩
    · rw [Language.vars_eq, Finset.mem_union] at hv'
      exact hv'.elim id id
    · simp at h
    · simp at h

/-! The unfolding substitution. -/

theorem foldl_max_ge : ∀ (l : List Var) (m : ℕ),
    m ≤ l.foldl (fun m x => max m x.id) m ∧ ∀ x ∈ l, x.id ≤ l.foldl (fun m x => max m x.id) m
  | [], m => ⟨le_rfl, by simp⟩
  | y :: l, m => by
    simp only [List.foldl_cons, List.mem_cons]
    obtain ⟨h1, h2⟩ := foldl_max_ge l (max m y.id)
    refine ⟨(le_max_left m y.id).trans h1, ?_⟩
    rintro x (rfl | hx)
    · exact (le_max_right m x.id).trans h1
    · exact h2 x hx

theorem Rules.other_not_mem (D : Def) : Rules.other D ∉ D.args ++ D.dummies := by
  intro h
  have := (foldl_max_ge (D.args ++ D.dummies) 0).2 _ h
  simp only [Rules.other] at this
  omega

theorem laterPairs_getElem : ∀ (ys : List Var) (p : Var × Var), p ∈ Rules.laterPairs ys →
    ∃ (j j' : ℕ), j < j' ∧ ys[j]? = some p.1 ∧ ys[j']? = some p.2
  | [], p, hp => by simp [Rules.laterPairs] at hp
  | y :: ys, p, hp => by
    simp only [Rules.laterPairs, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨y', hy', rfl⟩ | hp
    · obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.1 hy'
      exact ⟨0, j' + 1, by omega, by simp, by simpa using hj'⟩
    · obtain ⟨j, j', hjj, h1, h2⟩ := laterPairs_getElem ys p hp
      exact ⟨j + 1, j' + 1, by omega, by simpa using h1, by simpa using h2⟩

theorem Subst.assoc_append_of_mem {l l' : List (Var × Exp)} {v : Var} (hv : v ∈ l.map Prod.fst) :
    Subst.assoc (l ++ l') v = Subst.assoc l v := by
  unfold Subst.assoc
  rw [List.find?_append]
  have : (l.find? (fun p => decide (p.1 = v))).isSome := by
    rw [List.mem_map] at hv
    obtain ⟨p, hp, hpv⟩ := hv
    rw [List.find?_isSome]
    exact ⟨p, hp, by simpa using hpv⟩
  cases h : l.find? (fun p => decide (p.1 = v)) with
  | none => rw [h] at this; simp at this
  | some p => simp

/-- The map of a list by a substitution that agrees with the zip. -/
theorem map_f_of_zip (θ : Subst) : ∀ (l : List Var) (es : List Exp), l.length = es.length →
    (∀ p ∈ l.zip es, θ.f p.1 = p.2) → l.map θ.f = es
  | [], [], _, _ => rfl
  | x :: l, e :: es, hl, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [List.zip_cons_cons, List.mem_cons, forall_eq_or_imp] at h
    simp [h.1, map_f_of_zip θ l es hl h.2]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

end Lemmas


/-! ### The built trees are valid -/

section Valid

variable {L : Language} {db : Database} {st : Statement}

theorem forall₂_length {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → l₁.length = l₂.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [forall₂_length h]

theorem forall₂_zip {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ p ∈ l₁.zip l₂, R p.1 p.2
  | _, _, .nil, p, hp => by simp at hp
  | _, _, .cons h hs, p, hp => by
    simp only [List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact h
    · exact forall₂_zip hs p hp

/-- The claim about a built tree: valid, concluding the judgment, and with its
variables within `P`. -/
def BuiltOK (L : Language) (db : Database) (st : Statement) (T : PTree) (s : ℕ) (strict : Bool) (a b : Exp)
    (P : Var → Prop) : Prop :=
  Shape (db.withConv L) st T ∧ CondsHold (db.withConv L) st T ∧ T.expr = L.eq s strict a b ∧
    ∀ v ∈ T.allVars (db.withConv L), P v

/-- A position where two argument lists differ is regular. -/
theorem diff_regular {tys : List Ty} {es₁ es₂ : List Exp} (hl₁ : tys.length = es₁.length)
    (hl₂ : tys.length = es₂.length)
    (hnames : ∀ (j : ℕ) (u : Ty), tys[j]? = some u → u.name = true → es₁[j]? = es₂[j]?)
    {j : ℕ} (hne : es₁[j]? ≠ es₂[j]?) : j ∈ Rules.regularArgs tys := by
  have hj : j < tys.length := by
    by_contra h
    apply hne
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  obtain ⟨u, hu⟩ : ∃ u, tys[j]? = some u := ⟨tys[j], List.getElem?_eq_getElem hj⟩
  refine mem_regularArgs hu ?_
  by_contra hn
  exact hne (hnames j u hu (by simpa using hn))

theorem pick_isSome {strict : Bool} {es₁ es₂ : List Exp} (hne : strict = true → es₁ ≠ es₂)
    (hl : es₁.length = es₂.length) : (if strict then Build.firstDiff es₁ es₂ 0 else none).isSome = strict := by
  cases strict with
  | false => rfl
  | true =>
    obtain ⟨j, hj⟩ := firstDiff_some es₁ es₂ 0 (hne rfl) hl
    simp [hj]

/-- A congruence step is valid, given valid children; the common part of the two
directions, `as` and `bs` being the arguments of the two sides. -/
theorem congStep_ok {f : ℕ} {t : Ty} {as bs : List Exp} {s : ℕ} {strict : Bool} (hf : f < L.terms)
    (ht : t = ⟨L.sig.sort f, false⟩) (hs : s = L.sig.sort f)
    (hga : L.GoodArgs st.consts (L.sig.args f) as) (hgb : L.GoodArgs st.consts (L.sig.args f) bs)
    (hnames : ∀ (j : ℕ) (u : Ty), (L.sig.args f)[j]? = some u → u.name = true → as[j]? = bs[j]?)
    (hne : as ≠ bs) (hab : strict = true → as ≠ bs) (cs : List PTree) {Q : Var → Prop}
    (hcs : ∀ c ∈ cs, Shape (db.withConv L) st c ∧ CondsHold (db.withConv L) st c ∧
      ∀ v ∈ c.allVars (db.withConv L), Q v)
    (hcse : cs.map PTree.expr =
      (Rules.congHyps L (if strict then Build.firstDiff as bs 0 else none) (L.sig.args f)
        (Rules.congVars (L.sig.args f) 0).2.1 (Rules.congVars (L.sig.args f) 0).2.2 0).map
        (Subst.ofAssoc (Build.congAssoc (L.sig.args f) as bs 0)).apply) :
    BuiltOK L db st (.step (L.eq s strict (.app f t as) (.app f t bs))
      ((db.ruleIndex L (.cong f (if strict then Build.firstDiff as bs 0 else none))).getD 0)
      (Subst.ofAssoc (Build.congAssoc (L.sig.args f) as bs 0)) cs) s strict (.app f t as) (.app f t bs)
      (fun v => v ∈ Exp.varsOf as ∨ v ∈ Exp.varsOf bs ∨ Q v) := by
  obtain ⟨hl₁, _⟩ := Language.goodArgs_spec _ _ hga
  obtain ⟨hl₂, _⟩ := Language.goodArgs_spec _ _ hgb
  have hpickreg : ∀ i, (if strict then Build.firstDiff as bs 0 else none) = some i →
      i ∈ Rules.regularArgs (L.sig.args f) := by
    intro i hi
    cases strict with
    | false => simp at hi
    | true =>
      simp only [if_true] at hi
      exact diff_regular hl₁ hl₂ hnames (by simpa using (firstDiff_spec as bs 0 i hi).2)
  have hreg : ¬(Rules.regularArgs (L.sig.args f)).isEmpty = true := by
    obtain ⟨j, hj⟩ := firstDiff_some as bs 0 hne (hl₁.symm.trans hl₂)
    have := diff_regular hl₁ hl₂ hnames (by simpa using (firstDiff_spec as bs 0 j hj).2)
    intro h
    rw [List.isEmpty_iff] at h
    rw [h] at this
    simp at this
  obtain ⟨idx, hidx, _, A, hA, hspec⟩ := rule_at_index (db := db) (mem_all_cong hf hreg hpickreg db.defs)
  obtain ⟨rfl, _⟩ := hspec
  have hθ : ∀ p ∈ Build.congAssoc (L.sig.args f) as bs 0,
      (Subst.ofAssoc (Build.congAssoc (L.sig.args f) as bs 0)).f p.1 = p.2 :=
    fun p hp => Subst.ofAssoc_f_of_mem (congAssoc_nodup _ _ _ _) (by simpa using hp)
  obtain ⟨hap1, hap2⟩ := congVars_apply (L.sig.args f) as bs 0 _ hl₁ hl₂ hnames hθ
  have hsc : stepConds (db.withConv L) ((db.ruleIndex L (.cong f (if strict then Build.firstDiff as bs 0 else none))).getD 0)
      (Subst.ofAssoc (Build.congAssoc (L.sig.args f) as bs 0)) = [] := by
    rw [hidx, Option.getD_some]
    unfold stepConds
    rw [hA]
    rfl
  refine ⟨?_, ?_, rfl, ?_⟩
  · simp only [hidx, Option.getD_some]
    refine Shape.step _ _ _ _ _ hA ?_ ?_ ?_ ?_ (fun c hc => (hcs c hc).1)
    · exact Subst.ofAssoc_typed (congAssoc_fits _ _ _ _ hga hgb)
    · refine (Subst.ofAssoc_dom _).trans ?_
      rw [congAssoc_keys _ _ _ _ hl₁ hl₂]
      simp [Rules.congRule]
    · subst ht hs
      simp only [Rules.congRule, Language.apply_eq, Subst.apply_app, hap1, hap2,
        pick_isSome hab (hl₁.symm.trans hl₂)]
    · simpa [Rules.congRule] using hcse
  · intro k hk
    have hk' : k ∈ stepConds (db.withConv L) ((db.ruleIndex L (.cong f (if strict then Build.firstDiff as bs 0 else none))).getD 0)
        (Subst.ofAssoc (Build.congAssoc (L.sig.args f) as bs 0)) ++ PTree.condsList (db.withConv L) cs := hk
    rw [hsc, List.nil_append, PTree.mem_condsList] at hk'
    obtain ⟨c, hc, hk'⟩ := hk'
    exact (hcs c hc).2.1 k hk'
  · intro v hv
    rw [PTree.mem_allVars_step, hsc] at hv
    rcases hv with hv | ⟨_, h, _⟩ | ⟨c, hc, hv⟩
    · rw [Language.vars_eq, Finset.mem_union] at hv
      simp only [Exp.vars, Exp.mem_varsList, Exp.mem_varsOf] at hv ⊢
      rcases hv with hv | hv
      · exact Or.inl hv
      · exact Or.inr (Or.inl hv)
    · simp at h
    · exact Or.inr (Or.inr ((hcs c hc).2.2 v hv))

/-- An unfolding step and a folding step are valid: the common part of the two
directions. -/
theorem unfoldStep_ok {d : ℕ} {D : Def} (hD : db.defs[d]? = some D) (hwfD : D.WF) (hnd : st.consts.NameDeps)
    {es zs : List Exp} {b : Exp} {s : ℕ} (strict : Bool)
    (hes : List.Forall₂ (fun (x : Var) e => FitsTy x.ty e) D.args es)
    (hzs : List.Forall₂ (fun (y : Var) z => z.IsName ∧ z.ty = y.ty) D.dummies zs)
    (hapart : ∀ z ∈ zs, ∀ e ∈ es, z ∉ st.consts.names e) (hnodup : zs.Nodup)
    (hgz : ∀ z ∈ zs, L.Good st.consts z)
    (hb : b = (D.inst es zs).apply D.value) (hs : s = D.ty.sort) (hsb : b.ty.sort = s) (hslt : s < L.sorts) :
    BuiltOK L db st (.step (L.eq s strict (.app D.term D.ty es) b) ((db.ruleIndex L (.unfold d strict)).getD 0)
      (Subst.ofAssoc (Build.unfoldAssoc D es zs b)) [Build.reflTree L db s b]) s strict (.app D.term D.ty es) b
      (fun v => v ∈ Exp.varsOf es ∨ v ∈ Exp.varsOf zs ∨ v ∈ b.vars) ∧
    BuiltOK L db st (.step (L.eq s strict b (.app D.term D.ty es)) ((db.ruleIndex L (.fold d strict)).getD 0)
      (Subst.ofAssoc (Build.unfoldAssoc D es zs b)) [Build.reflTree L db s b]) s strict b (.app D.term D.ty es)
      (fun v => v ∈ Exp.varsOf es ∨ v ∈ Exp.varsOf zs ∨ v ∈ b.vars) := by
  have hl1 : D.args.length = es.length := forall₂_length hes
  have hl2 : D.dummies.length = zs.length := forall₂_length hzs
  have hkeys : (Build.unfoldAssoc D es zs b).map Prod.fst = D.args ++ D.dummies ++ [Rules.other D] := by
    simp [Build.unfoldAssoc, List.map_append, List.map_fst_zip hl1.le, List.map_fst_zip hl2.le]
  have hnd' : ((Build.unfoldAssoc D es zs b).map Prod.fst).Nodup := by
    rw [hkeys, List.nodup_append]
    refine ⟨hwfD.nodup, List.nodup_singleton _, fun a ha b' hb' => ?_⟩
    simp only [List.mem_singleton] at hb'
    subst hb'
    exact fun h => Rules.other_not_mem D (h ▸ ha)
  set θ := Subst.ofAssoc (Build.unfoldAssoc D es zs b) with hθdef
  have hθargs : ∀ p ∈ D.args.zip es, θ.f p.1 = p.2 := fun p hp =>
    Subst.ofAssoc_f_of_mem hnd' (by simp [Build.unfoldAssoc, hp])
  have hθdum : ∀ p ∈ D.dummies.zip zs, θ.f p.1 = p.2 := fun p hp =>
    Subst.ofAssoc_f_of_mem hnd' (by simp [Build.unfoldAssoc, hp])
  have hθo : θ.f (Rules.other D) = b := Subst.ofAssoc_f_of_mem hnd' (by simp [Build.unfoldAssoc])
  have hθval : θ.apply D.value = b := by
    rw [hb]
    apply apply_congr_vars
    intro v hv
    have hv' : v ∈ D.args ++ D.dummies := List.mem_toFinset.1 (hwfD.value_vars hv)
    show Subst.assoc (Build.unfoldAssoc D es zs b) v = Def.binding D es zs v
    unfold Build.unfoldAssoc
    rw [Subst.assoc_append_of_mem (by rw [List.map_append, List.map_fst_zip hl1.le, List.map_fst_zip hl2.le]; exact hv')]
    simp only [Def.binding, Subst.assoc, List.zip_append hl1]
    rfl
  have hθtyped : θ.Typed := by
    apply Subst.ofAssoc_typed
    intro p hp
    simp only [Build.unfoldAssoc, List.mem_append, List.mem_singleton] at hp
    rcases hp with (hp | hp) | rfl
    · exact forall₂_zip hes p hp
    · obtain ⟨hn, hty⟩ := forall₂_zip hzs p hp
      exact ⟨by rw [hty]; exact Ty.fits_refl _, fun _ => hn⟩
    · refine ⟨⟨?_, fun h => (Bool.false_ne_true h).elim⟩, fun h => (Bool.false_ne_true h).elim⟩
      show D.ty.sort = b.ty.sort
      rw [hsb, hs]
  have hmapargs : D.args.map θ.f = es := map_f_of_zip θ D.args es hl1 hθargs
  -- what the pairs of the step become: a dummy's name, and an argument's or a later dummy's
  have hdumAt : ∀ (j : ℕ) (y : Var), D.dummies[j]? = some y → ∃ hj : j < zs.length, θ.f y = zs[j] := by
    intro j y hj
    have hjz : j < zs.length := by rw [← hl2]; exact (List.getElem?_eq_some_iff.1 hj).1
    exact ⟨hjz, hθdum (y, zs[j]) (List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨hj, List.getElem?_eq_getElem hjz⟩))⟩
  have hargAt : ∀ (i : ℕ) (x : Var), D.args[i]? = some x → ∃ hi : i < es.length, θ.f x = es[i] := by
    intro i x hi
    have hie : i < es.length := by rw [← hl1]; exact (List.getElem?_eq_some_iff.1 hi).1
    exact ⟨hie, hθargs (x, es[i]) (List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨hi, List.getElem?_eq_getElem hie⟩))⟩
  have hpairs : ∀ p ∈ Rules.defPairs D, Cond.Holds st.consts (θ.f p.1, θ.f p.2) ∧
      θ.f p.1 ∈ zs ∧ (θ.f p.2 ∈ es ∨ θ.f p.2 ∈ zs) := by
    intro p hp
    simp only [Rules.defPairs, List.mem_append, List.mem_flatMap, List.mem_map] at hp
    rcases hp with ⟨y, hy, x, hx, rfl⟩ | hp
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hy
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
      obtain ⟨hjz, h1⟩ := hdumAt j y hj
      obtain ⟨hie, h2⟩ := hargAt i x hi
      refine ⟨?_, by rw [h1]; exact List.getElem_mem hjz, Or.inl (by rw [h2]; exact List.getElem_mem hie)⟩
      show θ.f y ∉ st.consts.names (θ.f x)
      rw [h1, h2]
      exact hapart _ (List.getElem_mem hjz) _ (List.getElem_mem hie)
    · obtain ⟨j, j', hjj, hj, hj'⟩ := laterPairs_getElem D.dummies p hp
      obtain ⟨hjz, h1⟩ := hdumAt j p.1 hj
      obtain ⟨hj'z, h2⟩ := hdumAt j' p.2 hj'
      have hy' : p.2 ∈ D.dummies := List.mem_of_getElem? hj'
      have hz' := forall₂_zip hzs (p.2, zs[j']) (List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨hj', List.getElem?_eq_getElem hj'z⟩))
      simp only [] at hz'
      have hty : (zs[j']).ty.name = true := by rw [hz'.2]; exact hwfD.dummies_name p.2 hy'
      have hne : zs[j] ≠ zs[j'] := List.pairwise_iff_getElem.1 hnodup j j' hjz hj'z hjj
      have hgood := hgz _ (List.getElem_mem hj'z)
      refine ⟨?_, by rw [h1]; exact List.getElem_mem hjz, Or.inr (by rw [h2]; exact List.getElem_mem hj'z)⟩
      show θ.f p.1 ∉ st.consts.names (θ.f p.2)
      rw [h1, h2, Consts.names_of_name hnd hz'.1 hty (fun k t hk => by rw [hk] at hgood; exact hgood.1)]
      exact hne
  have hrefl := reflTree_valid (db := db) (st := st) hslt hsb
  -- the two steps share everything but the rule
  have common : ∀ (k : RuleKind) (A : Assertion), (k, A) ∈ Rules.all L db.defs → A.pairs = Rules.defPairs D →
      ∀ (e : Exp) (idx : ℕ), db.ruleIndex L k = some idx → (db.withConv L).asserts[idx]? = some A →
      (CondsHold (db.withConv L) st (.step e ((db.ruleIndex L k).getD 0) θ [Build.reflTree L db s b]) ∧
       ∀ v ∈ (PTree.step e ((db.ruleIndex L k).getD 0) θ [Build.reflTree L db s b]).allVars (db.withConv L),
         v ∈ e.vars ∨ v ∈ Exp.varsOf es ∨ v ∈ Exp.varsOf zs ∨ v ∈ b.vars) := by
    intro k A _ hpairsA e idx hidx hA
    have hsc : stepConds (db.withConv L) ((db.ruleIndex L k).getD 0) θ =
        (Rules.defPairs D).map (fun p => (θ.f p.1, θ.f p.2)) := by
      rw [hidx, Option.getD_some]
      unfold stepConds
      rw [hA]
      show List.map (fun p => (θ.f p.1, θ.f p.2)) A.pairs = _
      rw [hpairsA]
    refine ⟨?_, ?_⟩
    · intro c hc
      have hc' : c ∈ stepConds (db.withConv L) ((db.ruleIndex L k).getD 0) θ ++
          PTree.condsList (db.withConv L) [Build.reflTree L db s b] := hc
      rw [hsc] at hc'
      simp only [List.mem_append, List.mem_map, PTree.condsList, List.append_nil] at hc'
      rcases hc' with ⟨p, hp, rfl⟩ | hc'
      · exact (hpairs p hp).1
      · exact hrefl.2.1 c hc'
    · intro v hv
      rw [PTree.mem_allVars_step, hsc] at hv
      rcases hv with hv | ⟨c, hc, hv⟩ | ⟨c, hc, hv⟩
      · exact Or.inl hv
      · simp only [List.mem_map] at hc
        obtain ⟨p, hp, rfl⟩ := hc
        obtain ⟨_, h1, h2⟩ := hpairs p hp
        simp only [Exp.mem_varsOf]
        rcases hv with hv | hv
        · exact Or.inr (Or.inr (Or.inl ⟨_, h1, hv⟩))
        · rcases h2 with h2 | h2
          · exact Or.inr (Or.inl ⟨_, h2, hv⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨_, h2, hv⟩))
      · simp only [List.mem_singleton] at hc
        subst hc
        exact Or.inr (Or.inr (Or.inr (hrefl.2.2.2 v hv)))
  refine ⟨?_, ?_⟩
  · obtain ⟨idx, hidx, _, A, hA, hspec⟩ := rule_at_index (L := L) (db := db) (mem_all_unfold (L := L) hD strict)
    obtain ⟨D', hD', rfl⟩ := hspec
    rw [hD] at hD'
    cases hD'
    obtain ⟨hconds, hvars⟩ := common _ _ (mem_all_unfold (L := L) hD strict) rfl _ idx hidx hA
    refine ⟨?_, hconds, rfl, ?_⟩
    · simp only [hidx, Option.getD_some]
      refine Shape.step _ _ _ _ _ hA hθtyped ?_ ?_ ?_ ?_
      · refine (Subst.ofAssoc_dom _).trans ?_
        rw [hkeys]
        simp [Rules.unfoldRule]
      · simp only [Rules.unfoldRule, Language.apply_eq, Rules.defApp, Subst.apply_app, List.map_map,
          Function.comp_def, Subst.apply_var, hmapargs, hθo, hs]
      · simp only [Rules.unfoldRule, List.map_cons, List.map_nil, Language.apply_eq, hθval, Subst.apply_var,
          hθo, hrefl.2.2.1]
        rw [hs]
      · intro c hc
        simp only [List.mem_singleton] at hc
        subst hc
        exact hrefl.1
    · intro v hv
      rcases hvars v hv with hv | hv
      · rw [Language.vars_eq, Finset.mem_union] at hv
        rcases hv with hv | hv
        · simp only [Exp.vars, Exp.mem_varsList, Exp.mem_varsOf] at hv ⊢
          exact Or.inl hv
        · exact Or.inr (Or.inr hv)
      · exact hv
  · obtain ⟨idx, hidx, _, A, hA, hspec⟩ := rule_at_index (L := L) (db := db) (mem_all_fold (L := L) hD strict)
    obtain ⟨D', hD', rfl⟩ := hspec
    rw [hD] at hD'
    cases hD'
    obtain ⟨hconds, hvars⟩ := common _ _ (mem_all_fold (L := L) hD strict) rfl _ idx hidx hA
    refine ⟨?_, hconds, rfl, ?_⟩
    · simp only [hidx, Option.getD_some]
      refine Shape.step _ _ _ _ _ hA hθtyped ?_ ?_ ?_ ?_
      · refine (Subst.ofAssoc_dom _).trans ?_
        rw [hkeys]
        simp [Rules.foldRule]
      · simp only [Rules.foldRule, Language.apply_eq, Rules.defApp, Subst.apply_app, List.map_map,
          Function.comp_def, Subst.apply_var, hmapargs, hθo, hs]
      · simp only [Rules.foldRule, List.map_cons, List.map_nil, Language.apply_eq, hθval, Subst.apply_var,
          hθo, hrefl.2.2.1]
        rw [hs]
      · intro c hc
        simp only [List.mem_singleton] at hc
        subst hc
        exact hrefl.1
    · intro v hv
      rcases hvars v hv with hv | hv
      · rw [Language.vars_eq, Finset.mem_union] at hv
        rcases hv with hv | hv
        · exact Or.inr (Or.inr hv)
        · simp only [Exp.vars, Exp.mem_varsList, Exp.mem_varsOf] at hv ⊢
          exact Or.inl hv
      · exact hv

/-- The variables of a certificate. -/
def CTree.vars (k : CTree) : Finset Var := Exp.varsOf k.exprs

/-- What the variables of a built tree are within: those of the two sides and of the
certificate. -/
def CertVars (k : CTree) (a b : Exp) (v : Var) : Prop := v ∈ a.vars ∨ v ∈ b.vars ∨ v ∈ k.vars

theorem certVars_symm {k : CTree} {a b : Exp} {v : Var} (h : CertVars k b a v) : CertVars (.symm k) a b v := by
  simp only [CertVars, CTree.vars, CTree.exprs] at h ⊢
  tauto

set_option maxHeartbeats 2000000 in
mutual
/-- The tree built from a certificate is valid and concludes the judgment. -/
theorem CTree.toTree_valid (hL : L.WF db st) (hdefs : db.DefsWF) (hnd : st.consts.NameDeps) :
    ∀ (k : CTree) (strict : Bool) (s : ℕ) (a b : Exp), CValid db L.sig st.consts k a b → k.NoTrans →
      L.Good st.consts a → L.Good st.consts b → (∀ x ∈ k.exprs, L.Good st.consts x) →
      a.ty.sort = s → b.ty.sort = s → (strict = true → a ≠ b) →
      BuiltOK L db st (k.toTree L db strict s a b) s strict a b (CertVars k a b)
  | .refl e, strict, s, a, b, hk, _, hga, _, _, hsa, _, hab => by
    cases hk
    cases strict with
    | true => exact absurd rfl (hab rfl)
    | false =>
      simp only [CTree.toTree]
      obtain ⟨h1, h2, h3, h4⟩ := reflTree_valid (db := db) (st := st) (hsa ▸ Language.good_sort hga) hsa
      exact ⟨h1, h2, h3, fun v hv => Or.inl (h4 v hv)⟩
  | .symm k, strict, s, a, b, hk, hnt, hga, hgb, hgk, hsa, hsb, hab => by
    cases hk with
    | symm hk' =>
      simp only [CTree.toTree]
      obtain ⟨h1, h2, h3, h4⟩ := CTree.toTreeR_valid hL hdefs hnd k strict s b a hk'
        (by simpa [CTree.NoTrans] using hnt) hgb hga (fun x hx => hgk x (by simp [CTree.exprs, hx])) hsb hsa
        (fun h => (hab h).symm)
      exact ⟨h1, h2, h3, fun v hv => certVars_symm (h4 v hv)⟩
  | .trans _ _, _, _, _, _, _, hnt, _, _, _, _, _, _ => absurd hnt (by simp [CTree.NoTrans])
  | .cong f t ks, strict, s, a, b, hk, hnt, hga, hgb, hgk, hsa, hsb, hab => by
    cases hk with
    | cong _ _ hks h₁ h₂ hnames =>
      rename_i es₁ es₂
      simp only [CTree.toTree]
      obtain ⟨hf, ht, hrs, hargs₁⟩ := hga
      obtain ⟨_, _, _, hargs₂⟩ := hgb
      by_cases heq : es₁ = es₂
      · subst heq
        rw [if_pos rfl]
        cases strict with
        | true => exact absurd rfl (hab rfl)
        | false =>
          obtain ⟨h1, h2, h3, h4⟩ := reflTree_valid (db := db) (st := st)
            (by rw [← hsa, ht]; exact hrs) hsa
          exact ⟨h1, h2, h3, fun v hv => Or.inl (h4 v hv)⟩
      · rw [if_neg heq]
        have hs : s = L.sig.sort f := by rw [← hsa, ht]; rfl
        have hθ : ∀ p ∈ Build.congAssoc (L.sig.args f) es₁ es₂ 0,
            (Subst.ofAssoc (Build.congAssoc (L.sig.args f) es₁ es₂ 0)).f p.1 = p.2 :=
          fun p hp => Subst.ofAssoc_f_of_mem (congAssoc_nodup _ _ _ _) (by simpa using hp)
        obtain ⟨hcs, hcse⟩ := CTree.toTreeList_valid hL hdefs hnd ks
          (if strict then Build.firstDiff es₁ es₂ 0 else none) (L.sig.args f) es₁ es₂ 0 0 _ hks
          (by simpa [CTree.NoTrans] using hnt)
          (fun k' hk' x hx => hgk x (by simp only [CTree.exprs]; exact (CTree.mem_exprsList ks).2 ⟨k', hk', hx⟩))
          hargs₁ hargs₂ hnames hθ (fun j hj _ => by
            cases strict with
            | false => simp at hj
            | true => simpa using (firstDiff_spec es₁ es₂ 0 j (by simpa using hj)).2)
        obtain ⟨h1, h2, h3, h4⟩ := congStep_ok hf ht hs hargs₁ hargs₂ hnames heq (fun h he => hab h (by rw [he])) _ hcs hcse
        refine ⟨h1, h2, h3, fun v hv => ?_⟩
        simp only [CertVars, CTree.vars, CTree.exprs, Exp.vars, Exp.mem_varsList, Exp.mem_varsOf]
        rcases h4 v hv with hv | hv | hv
        · simp only [Exp.mem_varsOf] at hv; exact Or.inl hv
        · simp only [Exp.mem_varsOf] at hv; exact Or.inr (Or.inl hv)
        · simp only [Exp.mem_varsOf] at hv
          rcases hv with hv | hv | hv
          · exact Or.inl hv
          · exact Or.inr (Or.inl hv)
          · exact Or.inr (Or.inr hv)
  | .unfold d es zs, strict, s, a, b, hk, _, hga, hgb, hgk, hsa, hsb, hab => by
    cases hk with
    | unfold hD hes hzs hapart hnodup =>
      rename_i D
      simp only [CTree.toTree, hD]
      have hwfD := hdefs D (List.mem_of_getElem? hD)
      have hs : s = D.ty.sort := by rw [← hsa]; rfl
      obtain ⟨h1, h2, h3, h4⟩ := (unfoldStep_ok hD hwfD hnd strict hes hzs hapart hnodup
        (fun z hz => hgk z (by simp [CTree.exprs, hz])) rfl hs hsb (hsa ▸ Language.good_sort hga)).1
      refine ⟨h1, h2, h3, fun v hv => ?_⟩
      simp only [CertVars, CTree.vars, CTree.exprs, Exp.vars, Exp.mem_varsList, Exp.mem_varsOf, List.mem_append]
      rcases h4 v hv with hv | hv | hv
      · simp only [Exp.mem_varsOf] at hv; exact Or.inl hv
      · simp only [Exp.mem_varsOf] at hv; obtain ⟨e, he, hv⟩ := hv; exact Or.inr (Or.inr ⟨e, Or.inr he, hv⟩)
      · exact Or.inr (Or.inl hv)
/-- The tree built from a certificate, backwards, is valid and concludes the reversed
judgment. -/
theorem CTree.toTreeR_valid (hL : L.WF db st) (hdefs : db.DefsWF) (hnd : st.consts.NameDeps) :
    ∀ (k : CTree) (strict : Bool) (s : ℕ) (a b : Exp), CValid db L.sig st.consts k a b → k.NoTrans →
      L.Good st.consts a → L.Good st.consts b → (∀ x ∈ k.exprs, L.Good st.consts x) →
      a.ty.sort = s → b.ty.sort = s → (strict = true → a ≠ b) →
      BuiltOK L db st (k.toTreeR L db strict s a b) s strict b a (CertVars k a b)
  | .refl e, strict, s, a, b, hk, _, hga, _, _, hsa, _, hab => by
    cases hk
    cases strict with
    | true => exact absurd rfl (hab rfl)
    | false =>
      simp only [CTree.toTreeR]
      obtain ⟨h1, h2, h3, h4⟩ := reflTree_valid (db := db) (st := st) (hsa ▸ Language.good_sort hga) hsa
      exact ⟨h1, h2, h3, fun v hv => Or.inl (h4 v hv)⟩
  | .symm k, strict, s, a, b, hk, hnt, hga, hgb, hgk, hsa, hsb, hab => by
    cases hk with
    | symm hk' =>
      simp only [CTree.toTreeR]
      obtain ⟨h1, h2, h3, h4⟩ := CTree.toTree_valid hL hdefs hnd k strict s b a hk'
        (by simpa [CTree.NoTrans] using hnt) hgb hga (fun x hx => hgk x (by simp [CTree.exprs, hx])) hsb hsa
        (fun h => (hab h).symm)
      exact ⟨h1, h2, h3, fun v hv => certVars_symm (h4 v hv)⟩
  | .trans _ _, _, _, _, _, _, hnt, _, _, _, _, _, _ => absurd hnt (by simp [CTree.NoTrans])
  | .cong f t ks, strict, s, a, b, hk, hnt, hga, hgb, hgk, hsa, hsb, hab => by
    cases hk with
    | cong _ _ hks h₁ h₂ hnames =>
      rename_i es₁ es₂
      simp only [CTree.toTreeR]
      obtain ⟨hf, ht, hrs, hargs₁⟩ := hga
      obtain ⟨_, _, _, hargs₂⟩ := hgb
      by_cases heq : es₁ = es₂
      · subst heq
        rw [if_pos rfl]
        cases strict with
        | true => exact absurd rfl (hab rfl)
        | false =>
          obtain ⟨h1, h2, h3, h4⟩ := reflTree_valid (db := db) (st := st)
            (by rw [← hsa, ht]; exact hrs) hsa
          exact ⟨h1, h2, h3, fun v hv => Or.inl (h4 v hv)⟩
      · rw [if_neg heq]
        have hs : s = L.sig.sort f := by rw [← hsa, ht]; rfl
        have hnames' : ∀ (j : ℕ) (u : Ty), (L.sig.args f)[j]? = some u → u.name = true → es₂[j]? = es₁[j]? :=
          fun j u hu hn => (hnames j u hu hn).symm
        have hθ : ∀ p ∈ Build.congAssoc (L.sig.args f) es₂ es₁ 0,
            (Subst.ofAssoc (Build.congAssoc (L.sig.args f) es₂ es₁ 0)).f p.1 = p.2 :=
          fun p hp => Subst.ofAssoc_f_of_mem (congAssoc_nodup _ _ _ _) (by simpa using hp)
        obtain ⟨hcs, hcse⟩ := CTree.toTreeListR_valid hL hdefs hnd ks
          (if strict then Build.firstDiff es₂ es₁ 0 else none) (L.sig.args f) es₁ es₂ 0 0 _ hks
          (by simpa [CTree.NoTrans] using hnt)
          (fun k' hk' x hx => hgk x (by simp only [CTree.exprs]; exact (CTree.mem_exprsList ks).2 ⟨k', hk', hx⟩))
          hargs₁ hargs₂ hnames hθ (fun j hj _ => by
            cases strict with
            | false => simp at hj
            | true => simpa using (firstDiff_spec es₂ es₁ 0 j (by simpa using hj)).2)
        obtain ⟨h1, h2, h3, h4⟩ := congStep_ok hf ht hs hargs₂ hargs₁ hnames' (fun h => heq h.symm)
          (fun h he => hab h (by rw [he])) _ hcs hcse
        refine ⟨h1, h2, h3, fun v hv => ?_⟩
        simp only [CertVars, CTree.vars, CTree.exprs, Exp.vars, Exp.mem_varsList, Exp.mem_varsOf]
        rcases h4 v hv with hv | hv | hv
        · simp only [Exp.mem_varsOf] at hv; exact Or.inr (Or.inl hv)
        · simp only [Exp.mem_varsOf] at hv; exact Or.inl hv
        · simp only [Exp.mem_varsOf] at hv
          rcases hv with hv | hv | hv
          · exact Or.inr (Or.inl hv)
          · exact Or.inl hv
          · exact Or.inr (Or.inr hv)
  | .unfold d es zs, strict, s, a, b, hk, _, hga, hgb, hgk, hsa, hsb, hab => by
    cases hk with
    | unfold hD hes hzs hapart hnodup =>
      rename_i D
      simp only [CTree.toTreeR, hD]
      have hwfD := hdefs D (List.mem_of_getElem? hD)
      have hs : s = D.ty.sort := by rw [← hsa]; rfl
      obtain ⟨h1, h2, h3, h4⟩ := (unfoldStep_ok hD hwfD hnd strict hes hzs hapart hnodup
        (fun z hz => hgk z (by simp [CTree.exprs, hz])) rfl hs hsb (hsa ▸ Language.good_sort hga)).2
      refine ⟨h1, h2, h3, fun v hv => ?_⟩
      simp only [CertVars, CTree.vars, CTree.exprs, Exp.vars, Exp.mem_varsList, Exp.mem_varsOf, List.mem_append]
      rcases h4 v hv with hv | hv | hv
      · simp only [Exp.mem_varsOf] at hv; exact Or.inl hv
      · simp only [Exp.mem_varsOf] at hv; obtain ⟨e, he, hv⟩ := hv; exact Or.inr (Or.inr ⟨e, Or.inr he, hv⟩)
      · exact Or.inr (Or.inl hv)
/-- The children of a congruence step are valid and conclude the rule's premises; their
variables are those of the arguments and of their certificates. -/
theorem CTree.toTreeList_valid (hL : L.WF db st) (hdefs : db.DefsWF) (hnd : st.consts.NameDeps) :
    ∀ (ks : List CTree) (pick : Option ℕ) (tys : List Ty) (es₁ es₂ : List Exp) (i kv : ℕ) (θ : Subst),
      CValidList db L.sig st.consts ks es₁ es₂ → (∀ k' ∈ ks, k'.NoTrans) →
      (∀ k' ∈ ks, ∀ x ∈ k'.exprs, L.Good st.consts x) →
      L.GoodArgs st.consts tys es₁ → L.GoodArgs st.consts tys es₂ →
      (∀ (j : ℕ) (u : Ty), tys[j]? = some u → u.name = true → es₁[j]? = es₂[j]?) →
      (∀ p ∈ Build.congAssoc tys es₁ es₂ kv, θ.f p.1 = p.2) →
      (∀ j, pick = some j → i ≤ j → es₁[j - i]? ≠ es₂[j - i]?) →
      (∀ c ∈ CTree.toTreeList L db pick tys ks es₁ es₂ i, Shape (db.withConv L) st c ∧ CondsHold (db.withConv L) st c ∧
        ∀ v ∈ c.allVars (db.withConv L), v ∈ Exp.varsOf es₁ ∨ v ∈ Exp.varsOf es₂ ∨ v ∈ Exp.varsOf (CTree.exprsList ks)) ∧
      (CTree.toTreeList L db pick tys ks es₁ es₂ i).map PTree.expr =
        (Rules.congHyps L pick tys (Rules.congVars tys kv).2.1 (Rules.congVars tys kv).2.2 i).map θ.apply
  | ks, pick, [], es₁, es₂, i, kv, θ, hks, _, _, hg₁, _, _, _, _ => by
    cases hks with
    | nil => simp [CTree.toTreeList, Rules.congHyps]
    | cons _ _ => simp [Language.GoodArgs] at hg₁
  | [], pick, ty :: tys, es₁, es₂, i, kv, θ, hks, _, _, hg₁, _, _, _, _ => by
    cases hks
    simp [Language.GoodArgs] at hg₁
  | k :: ks, pick, ty :: tys, [], es₂, i, kv, θ, hks, _, _, _, _, _, _, _ => by cases hks
  | k :: ks, pick, ty :: tys, e₁ :: es₁, [], i, kv, θ, hks, _, _, _, _, _, _, _ => by cases hks
  | k :: ks, pick, ty :: tys, e₁ :: es₁, e₂ :: es₂, i, kv, θ, hks, hnt, hgk, hg₁, hg₂, hnames, hθ, hpick => by
    cases hks with
    | cons hk hks' =>
      obtain ⟨f1, hs1, g1, hg₁'⟩ := hg₁
      obtain ⟨f2, _, g2, hg₂'⟩ := hg₂
      have hnames' : ∀ (j : ℕ) (u : Ty), tys[j]? = some u → u.name = true → es₁[j]? = es₂[j]? :=
        fun j u hu hn => by simpa using hnames (j + 1) u (by simpa using hu) hn
      have hpick' : ∀ j, pick = some j → i + 1 ≤ j → es₁[j - (i + 1)]? ≠ es₂[j - (i + 1)]? := by
        intro j hj hij
        have := hpick j hj (by omega)
        rw [show j - i = (j - (i + 1)) + 1 by omega] at this
        simpa using this
      have hwiden : ∀ v, (v ∈ Exp.varsOf es₁ ∨ v ∈ Exp.varsOf es₂ ∨ v ∈ Exp.varsOf (CTree.exprsList ks)) →
          v ∈ Exp.varsOf (e₁ :: es₁) ∨ v ∈ Exp.varsOf (e₂ :: es₂) ∨ v ∈ Exp.varsOf (CTree.exprsList (k :: ks)) := by
        intro v hv
        simp only [Exp.mem_varsOf, CTree.exprsList, List.mem_cons, List.mem_append] at hv ⊢
        aesop
      by_cases hn : ty.name = true
      · simp only [CTree.toTreeList, hn, if_true, List.nil_append]
        simp only [Rules.congHyps, Rules.congVars, hn, if_true, List.nil_append]
        simp only [Build.congAssoc, hn, if_true, List.mem_cons, forall_eq_or_imp] at hθ
        obtain ⟨hrest, hreste⟩ := CTree.toTreeList_valid hL hdefs hnd ks pick tys es₁ es₂ (i + 1) (kv + 1) θ hks'
          (fun k' hk' => hnt k' (by simp [hk'])) (fun k' hk' => hgk k' (by simp [hk'])) hg₁' hg₂' hnames' hθ.2 hpick'
        exact ⟨fun c hc => ⟨(hrest c hc).1, (hrest c hc).2.1, fun v hv => hwiden v ((hrest c hc).2.2 v hv)⟩, hreste⟩
      · simp only [CTree.toTreeList, hn, Bool.false_eq_true, if_false, List.singleton_append]
        simp only [Rules.congHyps, Rules.congVars, hn, Bool.false_eq_true, if_false, List.singleton_append]
        simp only [Build.congAssoc, hn, Bool.false_eq_true, if_false, List.mem_cons, forall_eq_or_imp] at hθ
        obtain ⟨hθ1, hθ2, hθ'⟩ := hθ
        have hab : (pick == some i) = true → e₁ ≠ e₂ := by
          intro h
          rw [beq_iff_eq] at h
          have := hpick i h le_rfl
          simpa using this
        have hchild := CTree.toTree_valid hL hdefs hnd k (pick == some i) ty.sort e₁ e₂ hk (hnt k (by simp))
          g1 g2 (hgk k (by simp)) f1.1.1.symm f2.1.1.symm hab
        obtain ⟨hrest, hreste⟩ := CTree.toTreeList_valid hL hdefs hnd ks pick tys es₁ es₂ (i + 1) (kv + 2) θ hks'
          (fun k' hk' => hnt k' (by simp [hk'])) (fun k' hk' => hgk k' (by simp [hk'])) hg₁' hg₂' hnames' hθ' hpick'
        refine ⟨?_, ?_⟩
        · intro c hc
          simp only [List.mem_cons] at hc
          rcases hc with rfl | hc
          · refine ⟨hchild.1, hchild.2.1, fun v hv => ?_⟩
            have := hchild.2.2.2 v hv
            simp only [CertVars, CTree.vars, Exp.mem_varsOf, CTree.exprsList, List.mem_cons, List.mem_append] at this ⊢
            aesop
          · exact ⟨(hrest c hc).1, (hrest c hc).2.1, fun v hv => hwiden v ((hrest c hc).2.2 v hv)⟩
        · simp only [List.map_cons, hchild.2.2.1, hreste, Language.apply_eq, Rules.v, Subst.apply_var, hθ1, hθ2]
/-- The same, backwards. -/
theorem CTree.toTreeListR_valid (hL : L.WF db st) (hdefs : db.DefsWF) (hnd : st.consts.NameDeps) :
    ∀ (ks : List CTree) (pick : Option ℕ) (tys : List Ty) (es₁ es₂ : List Exp) (i kv : ℕ) (θ : Subst),
      CValidList db L.sig st.consts ks es₁ es₂ → (∀ k' ∈ ks, k'.NoTrans) →
      (∀ k' ∈ ks, ∀ x ∈ k'.exprs, L.Good st.consts x) →
      L.GoodArgs st.consts tys es₁ → L.GoodArgs st.consts tys es₂ →
      (∀ (j : ℕ) (u : Ty), tys[j]? = some u → u.name = true → es₁[j]? = es₂[j]?) →
      (∀ p ∈ Build.congAssoc tys es₂ es₁ kv, θ.f p.1 = p.2) →
      (∀ j, pick = some j → i ≤ j → es₂[j - i]? ≠ es₁[j - i]?) →
      (∀ c ∈ CTree.toTreeListR L db pick tys ks es₁ es₂ i, Shape (db.withConv L) st c ∧ CondsHold (db.withConv L) st c ∧
        ∀ v ∈ c.allVars (db.withConv L), v ∈ Exp.varsOf es₂ ∨ v ∈ Exp.varsOf es₁ ∨ v ∈ Exp.varsOf (CTree.exprsList ks)) ∧
      (CTree.toTreeListR L db pick tys ks es₁ es₂ i).map PTree.expr =
        (Rules.congHyps L pick tys (Rules.congVars tys kv).2.1 (Rules.congVars tys kv).2.2 i).map θ.apply
  | ks, pick, [], es₁, es₂, i, kv, θ, hks, _, _, hg₁, _, _, _, _ => by
    cases hks with
    | nil => simp [CTree.toTreeListR, Rules.congHyps]
    | cons _ _ => simp [Language.GoodArgs] at hg₁
  | [], pick, ty :: tys, es₁, es₂, i, kv, θ, hks, _, _, hg₁, _, _, _, _ => by
    cases hks
    simp [Language.GoodArgs] at hg₁
  | k :: ks, pick, ty :: tys, [], es₂, i, kv, θ, hks, _, _, _, _, _, _, _ => by cases hks
  | k :: ks, pick, ty :: tys, e₁ :: es₁, [], i, kv, θ, hks, _, _, _, _, _, _, _ => by cases hks
  | k :: ks, pick, ty :: tys, e₁ :: es₁, e₂ :: es₂, i, kv, θ, hks, hnt, hgk, hg₁, hg₂, hnames, hθ, hpick => by
    cases hks with
    | cons hk hks' =>
      obtain ⟨f1, hs1, g1, hg₁'⟩ := hg₁
      obtain ⟨f2, _, g2, hg₂'⟩ := hg₂
      have hnames' : ∀ (j : ℕ) (u : Ty), tys[j]? = some u → u.name = true → es₁[j]? = es₂[j]? :=
        fun j u hu hn => by simpa using hnames (j + 1) u (by simpa using hu) hn
      have hpick' : ∀ j, pick = some j → i + 1 ≤ j → es₂[j - (i + 1)]? ≠ es₁[j - (i + 1)]? := by
        intro j hj hij
        have := hpick j hj (by omega)
        rw [show j - i = (j - (i + 1)) + 1 by omega] at this
        simpa using this
      have hwiden : ∀ v, (v ∈ Exp.varsOf es₂ ∨ v ∈ Exp.varsOf es₁ ∨ v ∈ Exp.varsOf (CTree.exprsList ks)) →
          v ∈ Exp.varsOf (e₂ :: es₂) ∨ v ∈ Exp.varsOf (e₁ :: es₁) ∨ v ∈ Exp.varsOf (CTree.exprsList (k :: ks)) := by
        intro v hv
        simp only [Exp.mem_varsOf, CTree.exprsList, List.mem_cons, List.mem_append] at hv ⊢
        aesop
      by_cases hn : ty.name = true
      · simp only [CTree.toTreeListR, hn, if_true, List.nil_append]
        simp only [Rules.congHyps, Rules.congVars, hn, if_true, List.nil_append]
        simp only [Build.congAssoc, hn, if_true, List.mem_cons, forall_eq_or_imp] at hθ
        obtain ⟨hrest, hreste⟩ := CTree.toTreeListR_valid hL hdefs hnd ks pick tys es₁ es₂ (i + 1) (kv + 1) θ hks'
          (fun k' hk' => hnt k' (by simp [hk'])) (fun k' hk' => hgk k' (by simp [hk'])) hg₁' hg₂' hnames' hθ.2 hpick'
        exact ⟨fun c hc => ⟨(hrest c hc).1, (hrest c hc).2.1, fun v hv => hwiden v ((hrest c hc).2.2 v hv)⟩, hreste⟩
      · simp only [CTree.toTreeListR, hn, Bool.false_eq_true, if_false, List.singleton_append]
        simp only [Rules.congHyps, Rules.congVars, hn, Bool.false_eq_true, if_false, List.singleton_append]
        simp only [Build.congAssoc, hn, Bool.false_eq_true, if_false, List.mem_cons, forall_eq_or_imp] at hθ
        obtain ⟨hθ1, hθ2, hθ'⟩ := hθ
        have hab : (pick == some i) = true → e₁ ≠ e₂ := by
          intro h
          rw [beq_iff_eq] at h
          have := hpick i h le_rfl
          simp only [Nat.sub_self, List.getElem?_cons_zero, ne_eq, Option.some.injEq] at this
          exact fun he => this he.symm
        have hchild := CTree.toTreeR_valid hL hdefs hnd k (pick == some i) ty.sort e₁ e₂ hk (hnt k (by simp))
          g1 g2 (hgk k (by simp)) f1.1.1.symm f2.1.1.symm hab
        obtain ⟨hrest, hreste⟩ := CTree.toTreeListR_valid hL hdefs hnd ks pick tys es₁ es₂ (i + 1) (kv + 2) θ hks'
          (fun k' hk' => hnt k' (by simp [hk'])) (fun k' hk' => hgk k' (by simp [hk'])) hg₁' hg₂' hnames' hθ' hpick'
        refine ⟨?_, ?_⟩
        · intro c hc
          simp only [List.mem_cons] at hc
          rcases hc with rfl | hc
          · refine ⟨hchild.1, hchild.2.1, fun v hv => ?_⟩
            have := hchild.2.2.2 v hv
            simp only [CertVars, CTree.vars, Exp.mem_varsOf, CTree.exprsList, List.mem_cons, List.mem_append] at this ⊢
            aesop
          · exact ⟨(hrest c hc).1, (hrest c hc).2.1, fun v hv => hwiden v ((hrest c hc).2.2 v hv)⟩
        · simp only [List.map_cons, hchild.2.2.1, hreste, Language.apply_eq, Rules.v, Subst.apply_var, hθ1, hθ2]
end

end Valid


/-! ### The proof -/

section Proof

variable {L : Language} {db : Database} {st : Statement}

theorem DTree.toPList_eq_map (L : Language) (db : Database) :
    ∀ cs : List DTree, DTree.toPList L db cs = cs.map (DTree.toP L db)
  | [] => rfl
  | t :: ts => by simp [DTree.toPList, DTree.toPList_eq_map L db ts]

theorem DTree.expr_toP (L : Language) (db : Database) : ∀ D : DTree, (D.toP L db).expr = D.expr
  | .hyp _ _ => rfl
  | .step _ _ _ _ => rfl
  | .conv e k t => by
    by_cases h : e = t.expr
    · simp only [DTree.toP]
      rw [if_pos h]
      show (DTree.toP L db t).expr = e
      rw [DTree.expr_toP L db t]
      exact h.symm
    · simp only [DTree.toP]
      rw [if_neg h]
      rfl

theorem DTree.expr_mem_exprs (db : Database) (D : DTree) : D.expr ∈ D.exprs db := by
  cases D <;> simp [DTree.expr, DTree.exprs]

theorem DTree.mem_condsList (db : Database) :
    ∀ (cs : List DTree) (k : Cond), k ∈ DTree.condsList db cs ↔ ∃ c ∈ cs, k ∈ c.conds db
  | [], k => by simp [DTree.condsList]
  | t :: ts, k => by
    simp only [DTree.condsList, List.mem_append, DTree.mem_condsList db ts, List.mem_cons]
    aesop

theorem DTree.Fits.child {e : Exp} {a : ℕ} {θ : Subst} {cs : List DTree}
    (hf : (DTree.step e a θ cs).Fits L db st) {c : DTree} (hc : c ∈ cs) : c.Fits L db st where
  good := fun x hx => hf.good x (by
    simp only [DTree.exprs, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inr ((DTree.mem_exprsList db cs).2 ⟨c, hc, hx⟩)))
  provable := fun x hx => hf.provable x (by
    simp only [DTree.nodeExprs, List.mem_cons, List.mem_flatMap]
    exact Or.inr ⟨c, hc, hx⟩)
  noTrans := fun k hk => hf.noTrans k (by
    simp only [DTree.certs, List.mem_flatMap]
    exact ⟨c, hc, hk⟩)

theorem DTree.Fits.conv {e : Exp} {k : CTree} {t : DTree} (hf : (DTree.conv e k t).Fits L db st) : t.Fits L db st where
  good := fun x hx => hf.good x (by simp [DTree.exprs, hx])
  provable := fun x hx => hf.provable x (by simp [DTree.nodeExprs, hx])
  noTrans := fun k' hk' => hf.noTrans k' (by simp [DTree.certs, hk'])

theorem Def.inst_f_eq_assoc (D : Def) (es zs : List Exp) (v : Var) :
    (D.inst es zs).f v = Subst.assoc ((D.args ++ D.dummies).zip (es ++ zs)) v := rfl

/-- The instance of a definition is typed when the arguments fit and the dummies are
names of their types. -/
theorem Def.inst_typed (D : Def) {es zs : List Exp}
    (hes : List.Forall₂ (fun (x : Var) e => FitsTy x.ty e) D.args es)
    (hzs : List.Forall₂ (fun (y : Var) z => z.IsName ∧ z.ty = y.ty) D.dummies zs) : (D.inst es zs).Typed := by
  intro v
  rw [Def.inst_f_eq_assoc]
  unfold Subst.assoc
  split
  · rename_i p hp
    have hmem := List.mem_of_find?_eq_some hp
    have hv : p.1 = v := by simpa using List.find?_some hp
    subst hv
    rw [List.zip_append (forall₂_length hes), List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact ⟨(forall₂_zip hes p hmem).1, (forall₂_zip hes p hmem).2⟩
    · obtain ⟨hn, hty⟩ := forall₂_zip hzs p hmem
      exact ⟨by rw [hty]; exact Ty.fits_refl _, fun _ => hn⟩
  · exact ⟨Ty.fits_refl _, fun _ => trivial⟩

/-- The two sides of a certificate have the same sort. -/
theorem CValid.sort_eq (hdefs : db.DefsWF) {sig : Signature} {c : Consts} :
    ∀ {k : CTree} {a b : Exp}, CValid db sig c k a b → a.ty.sort = b.ty.sort
  | .refl _, _, _, hk => by cases hk; rfl
  | .symm k', _, _, hk => by
    cases hk with
    | symm h => exact (CValid.sort_eq hdefs h).symm
  | .trans k₁ k₂, _, _, hk => by
    cases hk with
    | trans h1 h2 => exact (CValid.sort_eq hdefs h1).trans (CValid.sort_eq hdefs h2)
  | .cong _ _ _, _, _, hk => by cases hk; rfl
  | .unfold d es zs, _, _, hk => by
    cases hk with
    | unfold hD hes hzs hapart hnodup =>
      rename_i D
      have hwfD := hdefs D (List.mem_of_getElem? hD)
      show D.ty.sort = ((D.inst es zs).apply D.value).ty.sort
      rw [Subst.sort_apply (Def.inst_typed D hes hzs), hwfD.value_sort]

/-- An MM0 proof that fits the language stands for a valid tree over the extended
database, with its conditions and variables among the proof's. -/
theorem DTree.toP_valid (hL : L.WF db st) (hdefs : db.DefsWF) (hnd : st.consts.NameDeps) {D : DTree}
    (hs : DShape db L.sig st D) : DCondsHold db st D → D.Fits L db st →
      Shape (db.withConv L) st (D.toP L db) ∧ CondsHold (db.withConv L) st (D.toP L db) ∧
      ∀ v ∈ (D.toP L db).allVars (db.withConv L), v ∈ D.allVars db := by
  induction hs with
  | hyp h e hh he =>
    intro _ _
    refine ⟨Shape.hyp h e hh he, fun k hk => by simp [DTree.toP, PTree.conds] at hk, ?_⟩
    intro v hv
    simpa [DTree.toP, PTree.allVars, DTree.allVars, PTree.exprs, DTree.exprs] using hv
  | step e a θ cs A hA hθ hdom he hcs hall ih =>
    intro hc hf
    have hlt : a < db.asserts.length := (List.getElem?_eq_some_iff.1 hA).1
    have hA' : (db.withConv L).asserts[a]? = some A := by
      rw [Database.withConv_getElem?_lt L db hlt]; exact hA
    have hcc : ∀ c ∈ cs, DCondsHold db st c := fun c hc' k hk => hc k (by
      simp only [DTree.conds, List.mem_append]
      exact Or.inr ((DTree.mem_condsList db cs k).2 ⟨c, hc', hk⟩))
    have hfc : ∀ c ∈ cs, c.Fits L db st := fun c hc' => hf.child hc'
    refine ⟨?_, ?_, ?_⟩
    · simp only [DTree.toP]
      refine Shape.step e a θ _ A hA' hθ hdom he ?_ ?_
      · rw [DTree.toPList_eq_map, List.map_map, ← hcs]
        apply List.map_congr_left
        intro c _
        simp [DTree.expr_toP]
      · intro c' hc'
        rw [DTree.toPList_eq_map, List.mem_map] at hc'
        obtain ⟨c, hc', rfl⟩ := hc'
        exact (ih c hc' (hcc c hc') (hfc c hc')).1
    · intro k hk
      have hk' : k ∈ stepConds (db.withConv L) a θ ++ PTree.condsList (db.withConv L) (DTree.toPList L db cs) := hk
      rw [Database.stepConds_withConv_lt L db hlt, List.mem_append, PTree.mem_condsList] at hk'
      rcases hk' with hk' | ⟨c', hc', hk'⟩
      · exact hc k (by simp only [DTree.conds, List.mem_append]; exact Or.inl hk')
      · rw [DTree.toPList_eq_map, List.mem_map] at hc'
        obtain ⟨c, hc', rfl⟩ := hc'
        exact (ih c hc' (hcc c hc') (hfc c hc')).2.1 k hk'
    · intro v hv
      have hv' : v ∈ (PTree.step e a θ (DTree.toPList L db cs)).allVars (db.withConv L) := hv
      rw [PTree.mem_allVars_step, Database.stepConds_withConv_lt L db hlt] at hv'
      rw [DTree.mem_allVars]
      rcases hv' with hv' | ⟨k, hk, hv'⟩ | ⟨c', hc', hv'⟩
      · exact ⟨e, by simp [DTree.exprs], hv'⟩
      · rcases hv' with hv' | hv'
        · exact ⟨k.1, by
            simp only [DTree.exprs, List.mem_cons, List.mem_append, List.mem_flatMap]
            exact Or.inr (Or.inl ⟨k, hk, by simp⟩), hv'⟩
        · exact ⟨k.2, by
            simp only [DTree.exprs, List.mem_cons, List.mem_append, List.mem_flatMap]
            exact Or.inr (Or.inl ⟨k, hk, by simp⟩), hv'⟩
      · rw [DTree.toPList_eq_map, List.mem_map] at hc'
        obtain ⟨c, hc', rfl⟩ := hc'
        have := (ih c hc' (hcc c hc') (hfc c hc')).2.2 v hv'
        rw [DTree.mem_allVars] at this
        obtain ⟨x, hx, hvx⟩ := this
        exact ⟨x, by
          simp only [DTree.exprs, List.mem_cons, List.mem_append]
          exact Or.inr (Or.inr ((DTree.mem_exprsList db cs).2 ⟨c, hc', hx⟩)), hvx⟩
  | conv e k t hk ht ih =>
    intro hc hf
    have hct : DCondsHold db st t := hc
    have hft : t.Fits L db st := hf.conv
    obtain ⟨h1, h2, h3⟩ := ih hct hft
    simp only [DTree.toP]
    by_cases heq : e = t.expr
    · rw [if_pos heq]
      refine ⟨h1, h2, fun v hv => ?_⟩
      have := h3 v hv
      rw [DTree.mem_allVars] at this ⊢
      obtain ⟨x, hx, hvx⟩ := this
      exact ⟨x, by simp [DTree.exprs, hx], hvx⟩
    · rw [if_neg heq]
      have hge : L.Good st.consts e := hf.good e (by simp [DTree.exprs])
      have hgt : L.Good st.consts t.expr := hf.good t.expr (by
        simp only [DTree.exprs, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr (DTree.expr_mem_exprs db t)))
      have hgk : ∀ x ∈ k.exprs, L.Good st.consts x := fun x hx => hf.good x (by simp [DTree.exprs, hx])
      have hnt : k.NoTrans := hf.noTrans k (by simp [DTree.certs])
      have hprov : L.provable e.ty.sort = true := hf.provable e (by simp [DTree.nodeExprs])
      have hslt : e.ty.sort < L.sorts := Language.good_sort hge
      have hsort : t.expr.ty.sort = e.ty.sort := CValid.sort_eq hdefs hk
      obtain ⟨r1, r2, r3, r4⟩ := CTree.toTreeR_valid hL hdefs hnd k true e.ty.sort t.expr e hk hnt hgt hge hgk
        hsort rfl (fun _ h => heq h.symm)
      obtain ⟨idx, hidx, _, A, hA, hspec⟩ := rule_at_index (L := L) (db := db) (mem_all_conv hslt hprov db.defs)
      obtain ⟨rfl, _⟩ := hspec
      have hθ0 : (Subst.ofAssoc [(⟨0, ⟨e.ty.sort, false⟩⟩, e), (⟨1, ⟨e.ty.sort, false⟩⟩, t.expr)]).f
          ⟨0, ⟨e.ty.sort, false⟩⟩ = e := Subst.ofAssoc_f_of_mem (by simp) (by simp)
      have hθ1 : (Subst.ofAssoc [(⟨0, ⟨e.ty.sort, false⟩⟩, e), (⟨1, ⟨e.ty.sort, false⟩⟩, t.expr)]).f
          ⟨1, ⟨e.ty.sort, false⟩⟩ = t.expr := Subst.ofAssoc_f_of_mem (by simp) (by simp)
      have hsc : stepConds (db.withConv L) ((db.ruleIndex L (.conv e.ty.sort)).getD 0)
          (Subst.ofAssoc [(⟨0, ⟨e.ty.sort, false⟩⟩, e), (⟨1, ⟨e.ty.sort, false⟩⟩, t.expr)]) = [] := by
        rw [hidx, Option.getD_some]
        unfold stepConds
        rw [hA]
        rfl
      refine ⟨?_, ?_, ?_⟩
      · simp only [hidx, Option.getD_some]
        refine Shape.step _ _ _ _ _ hA ?_ ?_ ?_ ?_ ?_
        · exact Subst.ofAssoc_typed (by
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
              FitsTy]
            exact ⟨⟨⟨rfl, fun h => by simp at h⟩, fun h => by simp at h⟩,
              ⟨⟨hsort.symm, fun h => by simp at h⟩, fun h => by simp at h⟩⟩)
        · exact (Subst.ofAssoc_dom _).trans (by simp [Rules.convRule])
        · simp [Rules.convRule, Rules.v, Subst.apply_var, hθ0]
        · simp [Rules.convRule, Rules.v, Language.apply_eq, Subst.apply_var, hθ0, hθ1, DTree.expr_toP, r3]
        · intro c hc'
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc'
          rcases hc' with rfl | rfl
          · exact h1
          · exact r1
      · intro c hc'
        have hc'' : c ∈ stepConds (db.withConv L) ((db.ruleIndex L (.conv e.ty.sort)).getD 0)
            (Subst.ofAssoc [(⟨0, ⟨e.ty.sort, false⟩⟩, e), (⟨1, ⟨e.ty.sort, false⟩⟩, t.expr)]) ++
            PTree.condsList (db.withConv L) [DTree.toP L db t, CTree.toTreeR L db true e.ty.sort k t.expr e] := hc'
        rw [hsc, List.nil_append, PTree.mem_condsList] at hc''
        obtain ⟨c', hc', hcc'⟩ := hc''
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc'
        rcases hc' with rfl | rfl
        · exact h2 c hcc'
        · exact r2 c hcc'
      · intro v hv
        have hv' : v ∈ (PTree.step e ((db.ruleIndex L (.conv e.ty.sort)).getD 0)
            (Subst.ofAssoc [(⟨0, ⟨e.ty.sort, false⟩⟩, e), (⟨1, ⟨e.ty.sort, false⟩⟩, t.expr)])
            [DTree.toP L db t, CTree.toTreeR L db true e.ty.sort k t.expr e]).allVars (db.withConv L) := hv
        rw [PTree.mem_allVars_step, hsc] at hv'
        rw [DTree.mem_allVars]
        rcases hv' with hv' | ⟨_, h, _⟩ | ⟨c, hc', hv'⟩
        · exact ⟨e, by simp [DTree.exprs], hv'⟩
        · simp at h
        · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc'
          rcases hc' with rfl | rfl
          · have := h3 v hv'
            rw [DTree.mem_allVars] at this
            obtain ⟨x, hx, hvx⟩ := this
            exact ⟨x, by simp [DTree.exprs, hx], hvx⟩
          · rcases r4 v hv' with hv' | hv' | hv'
            · exact ⟨t.expr, by
                simp only [DTree.exprs, List.mem_cons, List.mem_append]
                exact Or.inr (Or.inr (DTree.expr_mem_exprs db t)), hv'⟩
            · exact ⟨e, by simp [DTree.exprs], hv'⟩
            · simp only [CTree.vars, Exp.mem_varsOf] at hv'
              obtain ⟨x, hx, hvx⟩ := hv'
              exact ⟨x, by simp [DTree.exprs, hx], hvx⟩

/-- An MM0 proof of the statement that fits the language stands for a proof of the
statement over the extended database. -/
theorem DTree.toP_isProof (hL : L.WF db st) (hdefs : db.DefsWF) (hnd : st.consts.NameDeps) {D : DTree}
    (h : IsProofD db L.sig st D) (hf : D.Fits L db st) : IsProof (db.withConv L) st (D.toP L db) := by
  obtain ⟨⟨hs, hc⟩, he, hv⟩ := h
  obtain ⟨h1, h2, h3⟩ := DTree.toP_valid hL hdefs hnd hs hc hf
  exact ⟨⟨h1, h2⟩, by rw [DTree.expr_toP, he], fun v hv' => hv v (h3 v hv')⟩

end Proof

end Theory
