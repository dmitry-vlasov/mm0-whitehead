/-
The theorems about the reference engine (`docs/THEORY.md`, "The theorems"): soundness,
generality and completeness, as the 2017 paper's Theorems 1–3 and the draft's 4.4–4.6,
for MM0 with its conditions on bound variables. Stated; the proofs are the milestones
2 to 4.
-/
import Theory.Search

namespace Theory

open State

/-- A statement without metavariables: its hypotheses and conclusion are over
constants only. -/
def Statement.Closed (st : Statement) : Prop :=
  st.concl.vars = ∅ ∧ ∀ h ∈ st.hyps, h.vars = ∅

/-- Soundness, the schematic form: the proof of an entry at the root is valid, and
proves the conclusion under the answer. -/
theorem soundness_valid (U : Unification) (db : Database) (st : Statement) (n : ℕ) :
    ∀ E ∈ (run U db st n).rootEntries,
      Valid db st (E.proof db (run U db st n)) ∧
      (E.proof db (run U db st n)).expr = E.sub.apply st.concl := by
  sorry

/-- Soundness: for a closed statement, every entry at the root has an instance that is
a proof of the statement — its variables left open given distinct fresh names. -/
theorem soundness (U : Unification) (db : Database) (st : Statement) (hst : st.Closed) (n : ℕ) :
    ∀ E ∈ (run U db st n).rootEntries,
      ∃ T : PTree, IsProof db st T ∧ T.IsInstance (E.proof db (run U db st n)) := by
  sorry

/-- Generality: the proof of an entry at the root is more general than every proof of
the statement congruent to it. -/
theorem generality (U : Unification) (db : Database) (st : Statement) (n : ℕ) :
    ∀ E ∈ (run U db st n).rootEntries, ∀ π : PTree,
      IsProof db st π → π.Congruent (E.proof db (run U db st n)) →
      π.IsInstance (E.proof db (run U db st n)) := by
  sorry

/-- Completeness: every proof of the statement is, after enough rounds, an instance of
the proof of an entry at the root congruent to it. -/
theorem completeness (U : Unification) (db : Database) (st : Statement) (π : PTree)
    (hπ : IsProof db st π) :
    ∃ n : ℕ, ∃ E ∈ (run U db st n).rootEntries,
      π.Congruent (E.proof db (run U db st n)) ∧ π.IsInstance (E.proof db (run U db st n)) := by
  sorry

end Theory
