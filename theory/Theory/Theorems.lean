/-
The theorems about the reference engine (`docs/THEORY.md`, "The theorems"): soundness,
generality and completeness, as the 2017 paper's Theorems 1–3 and the draft's 4.4–4.6,
for MM0 with its conditions on bound variables. Stated; the proofs are the milestones
2 to 4.

The statement may have metavariables (`Db.task` with `metas`): the root is an
expression node like any other, so what an entry at the root proves is the statement
under its answer, `st.subst E.sub`, and every theorem is about instances of the
statement. A statement without metavariables is the case where every instance is the
statement itself.
-/
import Theory.Search

namespace Theory

open State

/-- Soundness, the schematic form: the proof of an entry at the root is valid for the
statement under the answer, and proves its conclusion. -/
theorem soundness_valid (U : Unification) (db : Database) (st : Statement) (n : ℕ) :
    ∀ E ∈ (run U db st n).rootEntries,
      Valid db (st.subst E.sub) (E.proof db (run U db st n)) ∧
      (E.proof db (run U db st n)).expr = E.sub.apply st.concl := by
  sorry

/-- Soundness: every entry at the root has an instance that is a proof of the
statement under the answer — its variables left open given distinct fresh names,
which become the dummies. -/
theorem soundness (U : Unification) (db : Database) (st : Statement) (n : ℕ) :
    ∀ E ∈ (run U db st n).rootEntries, ∃ δ : Subst,
      IsProof db (st.subst (δ.comp E.sub)) ((E.proof db (run U db st n)).subst δ) := by
  sorry

/-- Generality: the proof of an entry at the root is more general than every proof of
an instance of the statement that is congruent to it. -/
theorem generality (U : Unification) (db : Database) (st : Statement) (n : ℕ) :
    ∀ E ∈ (run U db st n).rootEntries, ∀ (σ : Subst) (π : PTree),
      IsProof db (st.subst σ) π → π.Congruent (E.proof db (run U db st n)) →
      π.IsInstance (E.proof db (run U db st n)) := by
  sorry

/-- Completeness: every proof of an instance of the statement is, after enough rounds,
an instance of the proof of an entry at the root congruent to it. -/
theorem completeness (U : Unification) (db : Database) (st : Statement) (σ : Subst) (π : PTree)
    (hπ : IsProof db (st.subst σ) π) :
    ∃ n : ℕ, ∃ E ∈ (run U db st n).rootEntries,
      π.Congruent (E.proof db (run U db st n)) ∧ π.IsInstance (E.proof db (run U db st n)) := by
  sorry

end Theory
