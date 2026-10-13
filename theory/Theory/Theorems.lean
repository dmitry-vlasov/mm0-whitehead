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

/-- Closing (`PTree.close`) is a step of its own: a valid tree whose variables are of
sorts that allow dummies, with every variable made a dummy, is a proof of the statement
under the closing. Distinct fresh names satisfy every condition that holds under the
answer: a condition fails only when its name already occurs. -/
theorem close_isProof (db : Database) (st : Statement) (θ : Subst) (T : PTree)
    (hv : Valid db (st.subst θ) T) (he : T.expr = θ.apply st.concl)
    (hd : ∀ v ∈ T.vars, st.dummies v.ty.sort = true) :
    IsProof db (st.subst (T.closing.comp θ)) T.close := by
  sorry

/-- Soundness: the closing of the proof of every entry at the root is a proof of the
statement under the answer and the closing, when the sorts of the variables left allow
dummies. -/
theorem soundness (U : Unification) (db : Database) (st : Statement) (n : ℕ) :
    ∀ E ∈ (run U db st n).rootEntries,
      (∀ v ∈ (E.proof db (run U db st n)).vars, st.dummies v.ty.sort = true) →
      IsProof db (st.subst ((E.proof db (run U db st n)).closing.comp E.sub))
        (E.proof db (run U db st n)).close := by
  intro E hE hd
  obtain ⟨hv, he⟩ := soundness_valid U db st n E hE
  exact close_isProof db st E.sub _ hv he hd

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
