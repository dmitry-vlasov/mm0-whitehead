/-
Definitions in the model (`docs/THEORY.md`, "Definitions", milestone 8): the
conversion judgment of MM0 as the primary specification checks it (`examples/mm0.mm0`,
`VerifyConv`) — certificates with reflexivity, symmetry, transitivity, congruence and
the unfolding of a definition — and MM0 proofs with conversion steps (`VConv`), with
their validity. The engine never sees these: it searches over the judgment as
assertions (decision 10), and the two are linked by translation (milestones 9, 10).
The proofs of the first variant are MM0 proofs without conversion steps (`ofP`).
-/
import Theory.Deduction

namespace Theory

/-- A well-formed definition: its value is over its arguments and dummies, every dummy
occurs in the value (a dummy that did not would be a name an unfolding must choose and
no expression of a proof shows), the dummies are name-typed, the result is not a name
type, and no two binders are the same. -/
structure Def.WF (D : Def) : Prop where
  value_vars : D.value.vars ⊆ (D.args ++ D.dummies).toFinset
  dummies_used : ∀ y ∈ D.dummies, y ∈ D.value.vars
  dummies_name : ∀ y ∈ D.dummies, y.ty.name = true
  ty_name : D.ty.name = false
  /-- The value is of the sort of the result, and is no name. -/
  value_sort : D.value.ty.sort = D.ty.sort
  nodup : (D.args ++ D.dummies).Nodup

def Database.DefsWF (db : Database) : Prop := ∀ D ∈ db.defs, D.WF

/-- What a binder of a definition gets at an instance: the argument `x_i` the
expression `e_i`, the dummy `y_j` the name `z_j`; any other variable itself. -/
def Def.binding (D : Def) (es zs : List Exp) (v : Var) : Exp :=
  match ((D.args ++ D.dummies).zip (es ++ zs)).find? (fun p => decide (p.1 = v)) with
  | some p => p.2
  | none => .var v

theorem Def.binding_of_not_mem (D : Def) (es zs : List Exp) {v : Var}
    (hv : v ∉ D.args ++ D.dummies) : D.binding es zs v = .var v := by
  unfold Def.binding
  have : ((D.args ++ D.dummies).zip (es ++ zs)).find? (fun p => decide (p.1 = v)) = none := by
    rw [List.find?_eq_none]
    intro p hp h
    simp only [decide_eq_true_eq] at h
    exact hv (h ▸ (List.of_mem_zip hp).1)
  rw [this]

/-- The instance of a definition: its arguments given `es` and its dummies `zs`
(`mm0.mm0`: `substExpr (es ++ map SVar zs) val`). -/
def Def.inst (D : Def) (es zs : List Exp) : Subst :=
  Subst.ofFun (D.args ++ D.dummies).toFinset (D.binding es zs)
    (fun v hv => D.binding_of_not_mem es zs (by simpa using hv))

/-- A conversion certificate, `CExpr` of `mm0.mm0`: `CRefl`, `CSymm`, `CTrans`, `CCong`
with one certificate per argument, and `CUnfold f es zs`, the unfolding of the
definition `d` applied to `es`, with the names `zs` for its dummies. -/
inductive CTree where
  | refl (e : Exp)
  | symm (k : CTree)
  | trans (k₁ k₂ : CTree)
  | cong (f : ℕ) (t : Ty) (ks : List CTree)
  | unfold (d : ℕ) (es zs : List Exp)
  deriving Inhabited

/-- An expression fits the type of a binder: the same sort, and a name where names are
asked (`ExprBi` of `mm0.mm0`). -/
def FitsTy (t : Ty) (e : Exp) : Prop := t.fits e.ty ∧ (t.name = true → e.IsName)

mutual
/-- `CValid db sig c k e₁ e₂`: the certificate `k` converts `e₁` to `e₂`
(`VerifyConv env ctx k e₁ e₂`), over the signature for the typing of a congruence and
the constants of the statement for the names an argument has. The unfolding asks, as
the verifiers do (decision 9), that the dummies' names be apart from every argument
and from each other; a congruence, that the two sides of an argument that takes names
be the same name. -/
inductive CValid (db : Database) (sig : Signature) (c : Consts) : CTree → Exp → Exp → Prop
  | refl (e : Exp) : CValid db sig c (.refl e) e e
  | symm {k : CTree} {e₁ e₂ : Exp} : CValid db sig c k e₂ e₁ → CValid db sig c (.symm k) e₁ e₂
  | trans {k₁ k₂ : CTree} {e₁ e e₂ : Exp} :
      CValid db sig c k₁ e₁ e → CValid db sig c k₂ e e₂ → CValid db sig c (.trans k₁ k₂) e₁ e₂
  | cong (f : ℕ) (t : Ty) {ks : List CTree} {es₁ es₂ : List Exp}
      (hks : CValidList db sig c ks es₁ es₂)
      (h₁ : List.Forall₂ FitsTy (sig.args f) es₁) (h₂ : List.Forall₂ FitsTy (sig.args f) es₂)
      (hnames : ∀ (i : ℕ) (u : Ty), (sig.args f)[i]? = some u → u.name = true → es₁[i]? = es₂[i]?) :
      CValid db sig c (.cong f t ks) (.app f t es₁) (.app f t es₂)
  | unfold {d : ℕ} {D : Def} {es zs : List Exp}
      (hD : db.defs[d]? = some D)
      (hes : List.Forall₂ (fun (x : Var) e => FitsTy x.ty e) D.args es)
      (hzs : List.Forall₂ (fun (y : Var) z => z.IsName ∧ z.ty = y.ty) D.dummies zs)
      (hapart : ∀ z ∈ zs, ∀ e ∈ es, z ∉ c.names e)
      (hnodup : zs.Nodup) :
      CValid db sig c (.unfold d es zs) (.app D.term D.ty es) ((D.inst es zs).apply D.value)
/-- The certificates of the arguments of a congruence, each converting its argument. -/
inductive CValidList (db : Database) (sig : Signature) (c : Consts) : List CTree → List Exp → List Exp → Prop
  | nil : CValidList db sig c [] [] []
  | cons {k : CTree} {ks : List CTree} {e₁ e₂ : Exp} {es₁ es₂ : List Exp} :
      CValid db sig c k e₁ e₂ → CValidList db sig c ks es₁ es₂ →
      CValidList db sig c (k :: ks) (e₁ :: es₁) (e₂ :: es₂)
end

namespace CTree

mutual
/-- Every expression a certificate mentions. -/
def exprs : CTree → List Exp
  | refl e => [e]
  | symm k => exprs k
  | trans k₁ k₂ => exprs k₁ ++ exprs k₂
  | cong _ _ ks => exprsList ks
  | unfold _ es zs => es ++ zs
def exprsList : List CTree → List Exp
  | [] => []
  | k :: ks => exprs k ++ exprsList ks
end

end CTree

/-- An MM0 proof (`VExpr` of `mm0.mm0`): a hypothesis, an assertion step, or a
conversion `conv e k t`, `VConv k t`, proving `e` from `t` by `k : t.expr = e`. -/
inductive DTree where
  | hyp (h : ℕ) (e : Exp)
  | step (e : Exp) (a : ℕ) (θ : Subst) (children : List DTree)
  | conv (e : Exp) (k : CTree) (t : DTree)

instance : Inhabited DTree := ⟨.hyp 0 default⟩

namespace DTree

def expr : DTree → Exp
  | hyp _ e => e
  | step e _ _ _ => e
  | conv e _ _ => e

mutual
/-- The conditions of a proof: the pairs of every step under its substitution. A
conversion adds none: the conditions of an unfolding are judged in `CValid`. -/
def conds (db : Database) : DTree → List Cond
  | hyp _ _ => []
  | step _ a θ cs => stepConds db a θ ++ condsList db cs
  | conv _ _ t => conds db t
def condsList (db : Database) : List DTree → List Cond
  | [] => []
  | t :: ts => conds db t ++ condsList db ts
end

mutual
/-- Every expression of a proof: at its nodes, in its conditions, in its certificates. -/
def exprs (db : Database) : DTree → List Exp
  | hyp _ e => [e]
  | step e a θ cs => e :: (((stepConds db a θ).flatMap fun k => [k.1, k.2]) ++ exprsList db cs)
  | conv e k t => e :: (k.exprs ++ exprs db t)
def exprsList (db : Database) : List DTree → List Exp
  | [] => []
  | t :: ts => exprs db t ++ exprsList db ts
end

/-- The variables of a proof. -/
def allVars (db : Database) (T : DTree) : Finset Var :=
  (T.exprs db).foldr (fun e s => e.vars ∪ s) ∅

theorem mem_allVars (db : Database) (T : DTree) (v : Var) :
    v ∈ T.allVars db ↔ ∃ e ∈ T.exprs db, v ∈ e.vars := by
  unfold allVars
  induction T.exprs db with
  | nil => simp
  | cons e es ih => simp [ih]

end DTree

/-- Validity without the conditions, as `Shape` with a conversion step: a proof of `e`
from a proof of `t.expr` and a certificate from `t.expr` to `e`. -/
inductive DShape (db : Database) (sig : Signature) (st : Statement) : DTree → Prop
  | hyp (h : ℕ) (e : Exp) (hh : h < st.hyps.length) (he : e = st.hyps[h]!) : DShape db sig st (.hyp h e)
  | step (e : Exp) (a : ℕ) (θ : Subst) (cs : List DTree) (A : Assertion)
      (hA : db.asserts[a]? = some A) (hθ : θ.Typed) (hdom : θ.dom ⊆ A.vars.toFinset)
      (he : e = θ.apply A.concl)
      (hcs : cs.map DTree.expr = A.hyps.map θ.apply)
      (hall : ∀ c ∈ cs, DShape db sig st c) :
      DShape db sig st (.step e a θ cs)
  | conv (e : Exp) (k : CTree) (t : DTree) (hk : CValid db sig st.consts k t.expr e)
      (ht : DShape db sig st t) : DShape db sig st (.conv e k t)

def DCondsHold (db : Database) (st : Statement) (T : DTree) : Prop :=
  ∀ k ∈ T.conds db, k.Holds st.consts

/-- A valid MM0 proof tree: the shape, and the conditions. -/
def DValid (db : Database) (sig : Signature) (st : Statement) (T : DTree) : Prop :=
  DShape db sig st T ∧ DCondsHold db st T

/-- An MM0 proof of the statement: `IsProof` with conversion steps — valid, the
statement's conclusion at the root, every variable a dummy of a sort that allows
them. -/
def IsProofD (db : Database) (sig : Signature) (st : Statement) (T : DTree) : Prop :=
  DValid db sig st T ∧ T.expr = st.concl ∧ ∀ v ∈ T.allVars db, v.ty.name = true ∧ st.dummies v.ty.sort = true

/-! ### The proofs of the first variant are MM0 proofs -/

mutual
/-- A proof tree without conversion steps, as an MM0 proof. -/
def PTree.ofP : PTree → DTree
  | .hyp h e => .hyp h e
  | .step e a θ cs => .step e a θ (PTree.ofPList cs)
def PTree.ofPList : List PTree → List DTree
  | [] => []
  | t :: ts => PTree.ofP t :: PTree.ofPList ts
end

theorem PTree.ofPList_eq_map : ∀ cs : List PTree, PTree.ofPList cs = cs.map PTree.ofP
  | [] => rfl
  | t :: ts => by simp [PTree.ofPList, PTree.ofPList_eq_map ts]

theorem PTree.expr_ofP (T : PTree) : (T.ofP).expr = T.expr := by
  cases T <;> simp [PTree.ofP, PTree.expr, DTree.expr]

mutual
theorem PTree.conds_ofP (db : Database) : ∀ T : PTree, (T.ofP).conds db = T.conds db
  | .hyp _ _ => by simp [PTree.ofP, PTree.conds, DTree.conds]
  | .step _ a θ cs => by
    simp only [PTree.ofP, PTree.conds, DTree.conds, PTree.condsList_ofPList db cs]
theorem PTree.condsList_ofPList (db : Database) :
    ∀ cs : List PTree, DTree.condsList db (PTree.ofPList cs) = PTree.condsList db cs
  | [] => by simp [PTree.ofPList, PTree.condsList, DTree.condsList]
  | t :: ts => by
    simp only [PTree.ofPList, PTree.condsList, DTree.condsList, PTree.conds_ofP db t,
      PTree.condsList_ofPList db ts]
end

mutual
theorem PTree.exprs_ofP (db : Database) : ∀ T : PTree, (T.ofP).exprs db = T.exprs db
  | .hyp _ _ => by simp [PTree.ofP, PTree.exprs, DTree.exprs]
  | .step _ a θ cs => by
    simp only [PTree.ofP, PTree.exprs, DTree.exprs, PTree.exprsList_ofPList db cs]
theorem PTree.exprsList_ofPList (db : Database) :
    ∀ cs : List PTree, DTree.exprsList db (PTree.ofPList cs) = PTree.exprsList db cs
  | [] => by simp [PTree.ofPList, PTree.exprsList, DTree.exprsList]
  | t :: ts => by
    simp only [PTree.ofPList, PTree.exprsList, DTree.exprsList, PTree.exprs_ofP db t,
      PTree.exprsList_ofPList db ts]
end

theorem PTree.allVars_ofP (db : Database) (T : PTree) : (T.ofP).allVars db = T.allVars db := by
  simp [DTree.allVars, PTree.allVars, PTree.exprs_ofP]

theorem PTree.shape_ofP {db : Database} (sig : Signature) {st : Statement} {T : PTree}
    (h : Shape db st T) : DShape db sig st T.ofP := by
  induction h with
  | hyp h e hh he => exact DShape.hyp h e hh he
  | step e a θ cs A hA hθ hdom he hcs _ ih =>
    refine DShape.step e a θ _ A hA hθ hdom he ?_ ?_
    · rw [PTree.ofPList_eq_map, List.map_map, ← hcs]
      apply List.map_congr_left
      intro c _
      simp [PTree.expr_ofP]
    · intro c hc
      rw [PTree.ofPList_eq_map, List.mem_map] at hc
      obtain ⟨c', hc', rfl⟩ := hc
      exact ih c' hc'

/-- A proof of the statement in the first variant is an MM0 proof of it. -/
theorem PTree.isProofD_ofP {db : Database} (sig : Signature) {st : Statement} {T : PTree}
    (h : IsProof db st T) : IsProofD db sig st T.ofP := by
  obtain ⟨⟨hs, hc⟩, he, hv⟩ := h
  refine ⟨⟨PTree.shape_ofP sig hs, ?_⟩, ?_, ?_⟩
  · intro k hk
    rw [PTree.conds_ofP] at hk
    exact hc k hk
  · rw [PTree.expr_ofP, he]
  · intro v hv'
    rw [PTree.allVars_ofP] at hv'
    exact hv v hv'

end Theory
