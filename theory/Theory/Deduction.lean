/-
MM0 as a deductive system of the papers (`docs/THEORY.md`, "The model"): assertions
with their pairs of binders to keep apart, the statement being proved, proof trees and
their validity, instances and congruence.
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

/-- The statement being proved: its variables as constants (`Consts`), its hypotheses
and its conclusion, over constants and — for a task with metavariables — variables. -/
structure Statement where
  consts : Consts
  hyps : List Exp
  concl : Exp

/-- The statement under a substitution: an instance of it. For a statement with
metavariables, what a proof found proves; for one without, the statement itself. -/
def Statement.subst (σ : Subst) (st : Statement) : Statement :=
  { st with hyps := st.hyps.map σ.apply, concl := σ.apply st.concl }

/-- A substitution satisfies a pair `(x, v)`: the name given for `x` does not occur in
what is given for `v` (condition 2 of `DESIGN.md`, "Where MM0 differs"). -/
def SatPair (c : Consts) (θ : Subst) (p : Var × Var) : Prop :=
  θ.f p.1 ∉ c.names (θ.f p.2)

instance (c : Consts) (θ : Subst) (p : Var × Var) : Decidable (SatPair c θ p) := by
  unfold SatPair; infer_instance

/-- A condition carried by a proof: the name and the expression of a pair under the
substitutions so far. It holds when the name does not occur in the expression. -/
abbrev Cond := Exp × Exp

def Cond.Holds (c : Consts) (k : Cond) : Prop := k.1 ∉ c.names k.2

instance (c : Consts) (k : Cond) : Decidable (k.Holds c) := by unfold Cond.Holds; infer_instance

def Cond.apply (θ : Subst) (k : Cond) : Cond := (θ.apply k.1, θ.apply k.2)

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

mutual
/-- The variables of a tree. -/
def vars : PTree → Finset Var
  | hyp e => e.vars
  | step e _ _ cs => e.vars ∪ varsList cs
def varsList : List PTree → Finset Var
  | [] => ∅
  | t :: ts => vars t ∪ varsList ts
end

mutual
/-- The conditions of a tree: the pairs of every step under its substitution. -/
def conds (db : Database) : PTree → List Cond
  | hyp _ => []
  | step _ a θ cs =>
    (match db.asserts[a]? with
     | some A => A.pairs.map fun p => (θ.f p.1, θ.f p.2)
     | none => []) ++ condsList db cs
def condsList (db : Database) : List PTree → List Cond
  | [] => []
  | t :: ts => conds db t ++ condsList db ts
end

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

/-- The conditions of every step hold. -/
def CondsHold (db : Database) (st : Statement) (T : PTree) : Prop :=
  ∀ k ∈ T.conds db, k.Holds st.consts

/-- A valid proof tree: the shape, and the conditions. -/
def Valid (db : Database) (st : Statement) (T : PTree) : Prop :=
  Shape db st T ∧ CondsHold db st T

/-- A proof of the statement: a valid tree with the statement's conclusion at the
root, whose variables are all names — the dummies of the MM0 proof. -/
def IsProof (db : Database) (st : Statement) (T : PTree) : Prop :=
  Valid db st T ∧ T.expr = st.concl ∧ ∀ v ∈ T.vars, v.ty.name = true

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
