/-
MM0 as a deductive system of the papers (`docs/THEORY.md`, "The model"): assertions
with their pairs of binders to keep apart, the statement being proved, proof trees and
their validity, instances and congruence, and the closing of a proof.
-/
import Theory.Subst

namespace Theory

/-- An assertion: its binder variables (the variables `0, …, n-1` with their types),
the pairs `D(A)` of binders that a substitution must keep apart — `(x, v)` with `x`
bound, unless `v` is regular and declares `x` (`disjPairs` of `Whitehead/Prove/Db.lean`)
— its hypotheses and its conclusion. -/
structure Assertion where
  vars : List Var
  pairs : List (Var × Var)
  hyps : List Exp
  concl : Exp
  deriving Inhabited

/-- A definition `def f (xs) {.ys}: s = B` (`docs/THEORY.md`, "Definitions"): the term
it defines and its result type, its arguments and its dummies as variables, and its
value over both. -/
structure Def where
  term : ℕ
  ty : Ty
  args : List Var
  dummies : List Var
  value : Exp
  deriving Inhabited

/-- The assertions that may be used, by number; and the definitions of the file,
which the engine never reads (decision 10): it searches over the conversion judgment
as assertions, and `Defs.lean` has the judgment itself. -/
structure Database where
  asserts : List Assertion
  defs : List Def := []

/-- A well-formed assertion: its conclusion, hypotheses and pairs are over its
binders, and the first binder of every pair is bound, a name. -/
structure Assertion.WF (A : Assertion) : Prop where
  concl_vars : A.concl.vars ⊆ A.vars.toFinset
  hyps_vars : ∀ h ∈ A.hyps, h.vars ⊆ A.vars.toFinset
  pairs_vars : ∀ p ∈ A.pairs, p.1 ∈ A.vars ∧ p.2 ∈ A.vars
  pairs_bound : ∀ p ∈ A.pairs, p.1.ty.name = true

/-- A well-formed database: every assertion is. -/
def Database.WF (db : Database) : Prop := ∀ A ∈ db.asserts, A.WF

/-- The statement being proved: its variables as constants (`Consts`), the sorts whose
dummies a proof may use (`mm0.md`: neither `strict` nor `free`), its hypotheses and
its conclusion, over constants and — for a task with metavariables — variables. -/
structure Statement where
  consts : Consts
  dummies : ℕ → Bool
  hyps : List Exp
  concl : Exp

/-- The statement under a substitution: an instance of it. For a statement with
metavariables, what a proof found proves; for one without, the statement itself. -/
def Statement.subst (σ : Subst) (st : Statement) : Statement :=
  { st with hyps := st.hyps.map σ.apply, concl := σ.apply st.concl }

theorem Statement.subst_subst (st : Statement) (θ δ : Subst) :
    (st.subst θ).subst δ = st.subst (δ.comp θ) := by
  simp [Statement.subst, List.map_map, Function.comp_def, Subst.apply_comp]

/-- A substitution satisfies a pair `(x, v)`: the name given for `x` does not occur in
what is given for `v` (condition 2 of `DESIGN.md`, "Where MM0 differs"). -/
def SatPair (c : Consts) (θ : Subst) (p : Var × Var) : Prop :=
  θ.f p.1 ∉ c.names (θ.f p.2)

/-- A condition carried by a proof: the name and the expression of a pair under the
substitutions so far. It holds when the name does not occur in the expression. -/
abbrev Cond := Exp × Exp

def Cond.Holds (c : Consts) (k : Cond) : Prop := k.1 ∉ c.names k.2

instance (c : Consts) (k : Cond) : Decidable (k.Holds c) := by unfold Cond.Holds; infer_instance

def Cond.apply (θ : Subst) (k : Cond) : Cond := (θ.apply k.1, θ.apply k.2)

/-- The conditions of a step: the pairs of its assertion under its substitution. -/
def stepConds (db : Database) (a : ℕ) (θ : Subst) : List Cond :=
  match db.asserts[a]? with
  | some A => A.pairs.map fun p => (θ.f p.1, θ.f p.2)
  | none => []

theorem stepConds_comp (db : Database) (a : ℕ) (θ δ : Subst) :
    stepConds db a (δ.comp θ) = (stepConds db a θ).map (Cond.apply δ) := by
  unfold stepConds
  cases db.asserts[a]? <;> simp [Cond.apply, Subst.comp, List.map_map, Function.comp_def]

/-- A proof tree (the 2017 paper, section 2.3): an expression node with the assertion
node below it, or a leaf, which is a hypothesis of the statement, by its number and
with its expression. A step carries the substitution for the binders of its assertion,
and nothing else: `Shape` asks its domain to be among the binders. -/
inductive PTree where
  | hyp (h : ℕ) (e : Exp)
  | step (e : Exp) (a : ℕ) (θ : Subst) (children : List PTree)

instance : Inhabited PTree := ⟨.hyp 0 default⟩

namespace PTree

/-- The expression at the root. -/
def expr : PTree → Exp
  | hyp _ e => e
  | step e _ _ _ => e

/-- The binders of an assertion, as a set. -/
def binders (db : Database) (a : ℕ) : Finset Var := db.asserts[a]!.vars.toFinset

mutual
/-- The tree under a substitution: every expression, and every step's substitution
composed with it (component-wise, as the paper says), kept on the binders. -/
def subst (db : Database) (δ : Subst) : PTree → PTree
  | hyp h e => hyp h (δ.apply e)
  | step e a θ cs => step (δ.apply e) a ((δ.comp θ).restrict (binders db a)) (substList db δ cs)
def substList (db : Database) (δ : Subst) : List PTree → List PTree
  | [] => []
  | t :: ts => subst db δ t :: substList db δ ts
end

theorem substList_eq_map (db : Database) (δ : Subst) :
    ∀ cs : List PTree, substList db δ cs = cs.map (subst db δ)
  | [] => rfl
  | t :: ts => by simp [substList, substList_eq_map db δ ts]

theorem expr_subst (db : Database) (δ : Subst) (T : PTree) : (T.subst db δ).expr = δ.apply T.expr := by
  cases T <;> simp [subst, expr]

mutual
/-- The conditions of a tree: the pairs of every step under its substitution. -/
def conds (db : Database) : PTree → List Cond
  | hyp _ _ => []
  | step _ a θ cs => stepConds db a θ ++ condsList db cs
def condsList (db : Database) : List PTree → List Cond
  | [] => []
  | t :: ts => conds db t ++ condsList db ts
end

/-- The conditions of a step depend on the substitution at the binders only, in a
well-formed database. -/
theorem stepConds_restrict (db : Database) (hwf : db.WF) (a : ℕ) (θ : Subst) :
    stepConds db a (θ.restrict (binders db a)) = stepConds db a θ := by
  unfold stepConds
  cases hA : db.asserts[a]? with
  | none => rfl
  | some A =>
    have hA! : db.asserts[a]! = A := by
      obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hA
      exact getElem!_pos db.asserts a hi
    have hwfA := hwf A (List.mem_of_getElem? hA)
    apply List.map_congr_left
    intro p hp
    simp only [binders, hA!]
    rw [Subst.restrict_f_of_mem (List.mem_toFinset.2 (hwfA.pairs_vars p hp).1),
      Subst.restrict_f_of_mem (List.mem_toFinset.2 (hwfA.pairs_vars p hp).2)]

mutual
theorem conds_subst (db : Database) (hwf : db.WF) (δ : Subst) :
    ∀ T : PTree, (T.subst db δ).conds db = (T.conds db).map (Cond.apply δ)
  | hyp _ _ => by simp [subst, conds]
  | step _ a θ cs => by
    simp only [subst, conds, stepConds_restrict db hwf, stepConds_comp, condsList_substList db hwf δ cs,
      List.map_append]
theorem condsList_substList (db : Database) (hwf : db.WF) (δ : Subst) :
    ∀ cs : List PTree, condsList db (substList db δ cs) = (condsList db cs).map (Cond.apply δ)
  | [] => by simp [substList, condsList]
  | t :: ts => by
    simp only [substList, condsList, conds_subst db hwf δ t, condsList_substList db hwf δ ts, List.map_append]
end

mutual
/-- Every expression of a tree: at its nodes and in its conditions. -/
def exprs (db : Database) : PTree → List Exp
  | hyp _ e => [e]
  | step e a θ cs => e :: (((stepConds db a θ).flatMap fun k => [k.1, k.2]) ++ exprsList db cs)
def exprsList (db : Database) : List PTree → List Exp
  | [] => []
  | t :: ts => exprs db t ++ exprsList db ts
end

mutual
theorem exprs_subst (db : Database) (hwf : db.WF) (δ : Subst) :
    ∀ T : PTree, (T.subst db δ).exprs db = (T.exprs db).map δ.apply
  | hyp _ _ => by simp [subst, exprs]
  | step _ a θ cs => by
    simp only [subst, exprs, stepConds_restrict db hwf, stepConds_comp, exprsList_substList db hwf δ cs,
      List.map_cons, List.map_append, List.flatMap_map, List.map_flatMap]
    simp [Cond.apply]
theorem exprsList_substList (db : Database) (hwf : db.WF) (δ : Subst) :
    ∀ cs : List PTree, exprsList db (substList db δ cs) = (exprsList db cs).map δ.apply
  | [] => by simp [substList, exprsList]
  | t :: ts => by
    simp only [substList, exprsList, exprs_subst db hwf δ t, exprsList_substList db hwf δ ts, List.map_append]
end

theorem expr_mem_exprs (db : Database) (T : PTree) : T.expr ∈ T.exprs db := by
  cases T <;> simp [expr, exprs]

theorem condsList_eq_flatMap (db : Database) :
    ∀ cs : List PTree, condsList db cs = cs.flatMap (conds db)
  | [] => rfl
  | t :: ts => by simp [condsList, condsList_eq_flatMap db ts]

theorem mem_condsList (db : Database) :
    ∀ (cs : List PTree) (k : Cond), k ∈ condsList db cs ↔ ∃ c ∈ cs, k ∈ c.conds db
  | [], k => by simp [condsList]
  | t :: ts, k => by
    simp only [condsList, List.mem_append, mem_condsList db ts, List.mem_cons]
    aesop

mutual
theorem cond_mem_exprs (db : Database) :
    ∀ T : PTree, ∀ k ∈ T.conds db, k.1 ∈ T.exprs db ∧ k.2 ∈ T.exprs db
  | hyp _ _ => by simp [conds]
  | step _ a θ cs => by
    intro k hk
    simp only [conds, List.mem_append] at hk
    simp only [exprs, List.mem_cons, List.mem_append, List.mem_flatMap]
    rcases hk with hk | hk
    · exact ⟨Or.inr (Or.inl ⟨k, hk, by simp⟩), Or.inr (Or.inl ⟨k, hk, by simp⟩)⟩
    · obtain ⟨h1, h2⟩ := condList_mem_exprsList db cs k hk
      exact ⟨Or.inr (Or.inr h1), Or.inr (Or.inr h2)⟩
theorem condList_mem_exprsList (db : Database) :
    ∀ cs : List PTree, ∀ k ∈ condsList db cs, k.1 ∈ exprsList db cs ∧ k.2 ∈ exprsList db cs
  | [] => by simp [condsList]
  | t :: ts => by
    intro k hk
    simp only [condsList, List.mem_append] at hk
    simp only [exprsList, List.mem_append]
    rcases hk with hk | hk
    · obtain ⟨h1, h2⟩ := cond_mem_exprs db t k hk
      exact ⟨Or.inl h1, Or.inl h2⟩
    · obtain ⟨h1, h2⟩ := condList_mem_exprsList db ts k hk
      exact ⟨Or.inr h1, Or.inr h2⟩
end

/-- The variables of a tree: of every expression at its nodes and in its conditions. -/
def allVars (db : Database) (T : PTree) : Finset Var :=
  (T.exprs db).foldr (fun e s => e.vars ∪ s) ∅

theorem mem_allVars (db : Database) (T : PTree) (v : Var) :
    v ∈ T.allVars db ↔ ∃ e ∈ T.exprs db, v ∈ e.vars := by
  unfold allVars
  induction T.exprs db with
  | nil => simp
  | cons e es ih => simp [ih]

mutual
/-- The number of steps. -/
def size : PTree → ℕ
  | hyp _ _ => 0
  | step _ _ _ cs => sizeList cs + 1
def sizeList : List PTree → ℕ
  | [] => 0
  | t :: ts => size t + sizeList ts
end

end PTree

/-- Validity without the conditions: a leaf is a hypothesis of the statement; a step
is the instance of its assertion under a typed substitution, its children's expressions
the instances of the hypotheses in order. The paper's "proof"; the conditions on bound
variables are judged apart (`CondsHold`), so that monotonicity (Lemma 1) is about this
part alone. -/
inductive Shape (db : Database) (st : Statement) : PTree → Prop
  | hyp (h : ℕ) (e : Exp) (hh : h < st.hyps.length) (he : e = st.hyps[h]!) : Shape db st (.hyp h e)
  | step (e : Exp) (a : ℕ) (θ : Subst) (cs : List PTree) (A : Assertion)
      (hA : db.asserts[a]? = some A) (hθ : θ.Typed) (hdom : θ.dom ⊆ A.vars.toFinset)
      (he : e = θ.apply A.concl)
      (hcs : cs.map PTree.expr = A.hyps.map θ.apply)
      (hall : ∀ c ∈ cs, Shape db st c) :
      Shape db st (.step e a θ cs)

theorem getElem!_map' {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (l : List α) (k : ℕ)
    (hk : k < l.length) : (l.map f)[k]! = f l[k]! := by
  rw [getElem!_pos (l.map f) k (by simp [hk]), getElem!_pos l k hk]
  simp

/-- Monotonicity (the 2017 paper's Lemma 1): the shape is kept under a typed
substitution, applied to the tree and to the statement, in a well-formed database. -/
theorem Shape.subst {db : Database} (hwf : db.WF) {st : Statement} {T : PTree} (h : Shape db st T)
    {δ : Subst} (hδ : δ.Typed) : Shape db (st.subst δ) (T.subst db δ) := by
  induction h with
  | hyp h e hh he =>
    refine Shape.hyp h _ (by simp [Statement.subst, hh]) ?_
    simp only [Statement.subst]
    rw [getElem!_map' _ _ h hh, he]
  | step e a θ cs A hA hθ _ he hcs _ ih =>
    have hwfA := hwf A (List.mem_of_getElem? hA)
    have hA! : db.asserts[a]! = A := by
      obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hA
      exact getElem!_pos db.asserts a hi
    have hb : PTree.binders db a = A.vars.toFinset := by simp [PTree.binders, hA!]
    refine Shape.step _ a _ _ A hA ((Subst.Typed.comp hδ hθ).restrict _) ?_ ?_ ?_ ?_
    · rw [hb]; exact Subst.restrict_dom_subset _ _
    · rw [he, hb, Subst.restrict_apply A.concl hwfA.concl_vars, Subst.apply_comp]
    · rw [PTree.substList_eq_map, List.map_map]
      have h1 : PTree.expr ∘ PTree.subst db δ = δ.apply ∘ PTree.expr := by
        funext c; simp [PTree.expr_subst]
      rw [h1, ← List.map_map, hcs, List.map_map]
      apply List.map_congr_left
      intro x hx
      simp only [Function.comp]
      rw [hb, Subst.restrict_apply x (hwfA.hyps_vars x hx), Subst.apply_comp]
    · intro c hc
      rw [PTree.substList_eq_map, List.mem_map] at hc
      obtain ⟨c', hc', rfl⟩ := hc
      exact ih c' hc'

/-- The conditions of every step hold. -/
def CondsHold (db : Database) (st : Statement) (T : PTree) : Prop :=
  ∀ k ∈ T.conds db, k.Holds st.consts

/-- A valid proof tree: the shape, and the conditions. -/
def Valid (db : Database) (st : Statement) (T : PTree) : Prop :=
  Shape db st T ∧ CondsHold db st T

/-- A proof of the statement: a valid tree with the statement's conclusion at the
root, whose variables are all names of sorts that allow dummies — the dummies of the
MM0 proof (`Dummy` in the `.mmb`). -/
def IsProof (db : Database) (st : Statement) (T : PTree) : Prop :=
  Valid db st T ∧ T.expr = st.concl ∧ ∀ v ∈ T.allVars db, v.ty.name = true ∧ st.dummies v.ty.sort = true

/-- The dummy that closing gives a variable: a name of its sort, numbered by `code`, so
that distinct variables get distinct dummies. -/
def Var.dummy (v : Var) : Var := ⟨v.code, ⟨v.ty.sort, true⟩⟩

theorem Var.dummy_injective : Function.Injective Var.dummy := by
  intro a b h
  exact Var.code_injective (congrArg Var.id h)

/-- The closing of a tree, a step apart from the search (`docs/THEORY.md`, decision 8):
every variable left becomes its dummy. -/
def PTree.closing (db : Database) (T : PTree) : Subst :=
  Subst.ofFun (T.allVars db) (fun v => if v ∈ T.allVars db then .var v.dummy else .var v)
    (fun v hv => by simp [hv])

def PTree.close (db : Database) (T : PTree) : PTree := T.subst db (T.closing db)

/-- `T'` is an instance of `T`: `T' = δ(T)` (the paper's `T ≽ T'`). -/
def PTree.IsInstance (db : Database) (T' T : PTree) : Prop := ∃ δ : Subst, T' = T.subst db δ

mutual
/-- Congruent: the same shape with the same assertions and the same hypotheses at the
leaves (the paper, section 2.3; the draft, Proposition 3.7). -/
def PTree.Congruent : PTree → PTree → Prop
  | .hyp h _, .hyp h' _ => h = h'
  | .step _ a _ cs, .step _ a' _ cs' => a = a' ∧ PTree.CongruentList cs cs'
  | _, _ => False
def PTree.CongruentList : List PTree → List PTree → Prop
  | [], [] => True
  | t :: ts, t' :: ts' => PTree.Congruent t t' ∧ PTree.CongruentList ts ts'
  | _, _ => False
end

end Theory
