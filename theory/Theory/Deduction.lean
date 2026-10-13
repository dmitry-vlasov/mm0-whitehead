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

/-- The assertions that may be used, by number. -/
structure Database where
  asserts : List Assertion

/-- A well-formed database: the first binder of every pair is bound, a name. -/
def Database.WF (db : Database) : Prop :=
  ∀ A ∈ db.asserts, ∀ p ∈ A.pairs, p.1.ty.name = true

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
node below it, or a leaf, which is a hypothesis of the statement. A step carries the
substitution for the binders of its assertion. -/
inductive PTree where
  | hyp (e : Exp)
  | step (e : Exp) (a : ℕ) (θ : Subst) (children : List PTree)

namespace PTree

/-- The expression at the root. -/
def expr : PTree → Exp
  | hyp e => e
  | step e _ _ _ => e

mutual
/-- The tree under a substitution: every expression, and every step's substitution
composed with it (component-wise, as the paper says). -/
def subst (δ : Subst) : PTree → PTree
  | hyp e => hyp (δ.apply e)
  | step e a θ cs => step (δ.apply e) a (δ.comp θ) (substList δ cs)
def substList (δ : Subst) : List PTree → List PTree
  | [] => []
  | t :: ts => subst δ t :: substList δ ts
end

theorem substList_eq_map (δ : Subst) : ∀ cs : List PTree, substList δ cs = cs.map (subst δ)
  | [] => rfl
  | t :: ts => by simp [substList, substList_eq_map δ ts]

theorem expr_subst (δ : Subst) (T : PTree) : (T.subst δ).expr = δ.apply T.expr := by
  cases T <;> simp [subst, expr]

mutual
/-- The conditions of a tree: the pairs of every step under its substitution. -/
def conds (db : Database) : PTree → List Cond
  | hyp _ => []
  | step _ a θ cs => stepConds db a θ ++ condsList db cs
def condsList (db : Database) : List PTree → List Cond
  | [] => []
  | t :: ts => conds db t ++ condsList db ts
end

mutual
theorem conds_subst (db : Database) (δ : Subst) :
    ∀ T : PTree, (T.subst δ).conds db = (T.conds db).map (Cond.apply δ)
  | hyp _ => by simp [subst, conds]
  | step _ a θ cs => by
    simp only [subst, conds, stepConds_comp, condsList_substList db δ cs, List.map_append]
theorem condsList_substList (db : Database) (δ : Subst) :
    ∀ cs : List PTree, condsList db (substList δ cs) = (condsList db cs).map (Cond.apply δ)
  | [] => by simp [substList, condsList]
  | t :: ts => by
    simp only [substList, condsList, conds_subst db δ t, condsList_substList db δ ts, List.map_append]
end

mutual
/-- Every expression of a tree: at its nodes and in its conditions. -/
def exprs (db : Database) : PTree → List Exp
  | hyp e => [e]
  | step e a θ cs => e :: (((stepConds db a θ).flatMap fun k => [k.1, k.2]) ++ exprsList db cs)
def exprsList (db : Database) : List PTree → List Exp
  | [] => []
  | t :: ts => exprs db t ++ exprsList db ts
end

mutual
theorem exprs_subst (db : Database) (δ : Subst) :
    ∀ T : PTree, (T.subst δ).exprs db = (T.exprs db).map δ.apply
  | hyp _ => by simp [subst, exprs]
  | step _ a θ cs => by
    simp only [subst, exprs, stepConds_comp, exprsList_substList db δ cs, List.map_cons, List.map_append,
      List.flatMap_map, List.map_flatMap]
    simp [Cond.apply]
theorem exprsList_substList (db : Database) (δ : Subst) :
    ∀ cs : List PTree, exprsList db (substList δ cs) = (exprsList db cs).map δ.apply
  | [] => by simp [substList, exprsList]
  | t :: ts => by
    simp only [substList, exprsList, exprs_subst db δ t, exprsList_substList db δ ts, List.map_append]
end

theorem expr_mem_exprs (db : Database) (T : PTree) : T.expr ∈ T.exprs db := by
  cases T <;> simp [expr, exprs]

theorem mem_condsList (db : Database) :
    ∀ (cs : List PTree) (k : Cond), k ∈ condsList db cs ↔ ∃ c ∈ cs, k ∈ c.conds db
  | [], k => by simp [condsList]
  | t :: ts, k => by
    simp only [condsList, List.mem_append, mem_condsList db ts, List.mem_cons]
    aesop

mutual
theorem cond_mem_exprs (db : Database) :
    ∀ T : PTree, ∀ k ∈ T.conds db, k.1 ∈ T.exprs db ∧ k.2 ∈ T.exprs db
  | hyp _ => by simp [conds]
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
  | hyp _ => 0
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
  | hyp (e : Exp) (h : e ∈ st.hyps) : Shape db st (.hyp e)
  | step (e : Exp) (a : ℕ) (θ : Subst) (cs : List PTree) (A : Assertion)
      (hA : db.asserts[a]? = some A) (hθ : θ.Typed) (he : e = θ.apply A.concl)
      (hcs : cs.map PTree.expr = A.hyps.map θ.apply)
      (hall : ∀ c ∈ cs, Shape db st c) :
      Shape db st (.step e a θ cs)

/-- Monotonicity (the 2017 paper's Lemma 1): the shape is kept under a typed
substitution, applied to the tree and to the statement. -/
theorem Shape.subst {db : Database} {st : Statement} {T : PTree} (h : Shape db st T)
    {δ : Subst} (hδ : δ.Typed) : Shape db (st.subst δ) (T.subst δ) := by
  induction h with
  | hyp e he => exact Shape.hyp _ (List.mem_map_of_mem he)
  | step e a θ cs A hA hθ he hcs _ ih =>
    refine Shape.step _ a (δ.comp θ) _ A hA (Subst.Typed.comp hδ hθ) ?_ ?_ ?_
    · rw [he, Subst.apply_comp]
    · rw [PTree.substList_eq_map, List.map_map]
      have h1 : PTree.expr ∘ PTree.subst δ = δ.apply ∘ PTree.expr := by
        funext c; simp [PTree.expr_subst]
      rw [h1, ← List.map_map, hcs, List.map_map]
      congr 1
      funext x
      simp [Subst.apply_comp]
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

def PTree.close (db : Database) (T : PTree) : PTree := T.subst (T.closing db)

/-- `T'` is an instance of `T`: `T' = δ(T)` (the paper's `T ≽ T'`). -/
def PTree.IsInstance (T' T : PTree) : Prop := ∃ δ : Subst, T' = T.subst δ

mutual
/-- Congruent: the same shape with the same assertions (the paper, section 2.3). -/
def PTree.Congruent : PTree → PTree → Prop
  | .hyp _, .hyp _ => True
  | .step _ a _ cs, .step _ a' _ cs' => a = a' ∧ PTree.CongruentList cs cs'
  | _, _ => False
def PTree.CongruentList : List PTree → List PTree → Prop
  | [], [] => True
  | t :: ts, t' :: ts' => PTree.Congruent t t' ∧ PTree.CongruentList ts ts'
  | _, _ => False
end

end Theory
