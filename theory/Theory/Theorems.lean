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
import Theory.Closing
import Theory.Preserve
import Theory.Generality
import Theory.Completeness
import Theory.ToD

namespace Theory

open State

/-- Soundness, the schematic form: the proof of an entry at the root is valid for the
statement under the answer, and proves its conclusion. The state after any number of
rounds has the invariants (`run_inv`), every entry of its SPT sets has the entry
invariant (`sptE_inv`), and an entry with it is a valid proof (`valid_of_inv`). -/
theorem soundness_valid (U : Unification) (db : Database) (hwf : db.WF) (st : Statement) (n : ℕ) :
    ∀ E ∈ (run U db st n).rootEntries U st,
      Valid db (st.subst E.sub) (E.proof db (run U db st n)) ∧
      (E.proof db (run U db st n)).expr = E.sub.apply st.concl := by
  intro E hE
  have hs := run_inv U db hwf st n
  exact valid_of_inv hwf hs E (sptE_inv hs _ 0 hs.root_lt E hE)

/-- Soundness: the closing of the proof of every entry at the root is a proof of the
statement under the answer and the closing, when the sorts of the variables left allow
dummies (`close_isProof`, `Closing.lean`). -/
theorem soundness (U : Unification) (db : Database) (hwf : db.WF) (st : Statement) (n : ℕ) :
    ∀ E ∈ (run U db st n).rootEntries U st,
      (∀ v ∈ (E.proof db (run U db st n)).allVars db, st.dummies v.ty.sort = true) →
      IsProof db (st.subst (((E.proof db (run U db st n)).closing db).comp E.sub))
        ((E.proof db (run U db st n)).close db) := by
  intro E hE hd
  obtain ⟨hv, he⟩ := soundness_valid U db hwf st n E hE
  exact close_isProof db hwf st E.sub _ hv he hd

/-- Generality: the proof of an entry at the root is more general than every proof of
an instance of the statement that is congruent to it (`Generality.lean`). -/
theorem generality (U : Unification) (db : Database) (hwf : db.WF) (st : Statement) (n : ℕ) :
    ∀ E ∈ (run U db st n).rootEntries U st, ∀ (σ : Subst), σ.Typed → ∀ (π : PTree),
      IsProof db (st.subst σ) π → π.Congruent (E.proof db (run U db st n)) →
      π.IsInstance db (E.proof db (run U db st n)) :=
  generality' hwf n

/-- Completeness: every proof of an instance of the statement is, after enough rounds,
an instance of the proof of an entry at the root congruent to it (`Completeness.lean`). -/
theorem completeness (U : Unification) (db : Database) (hwf : db.WF) (st : Statement) (σ : Subst)
    (hσ : σ.Typed) (π : PTree) (hπ : IsProof db (st.subst σ) π) :
    ∃ n : ℕ, ∃ E ∈ (run U db st n).rootEntries U st,
      π.Congruent (E.proof db (run U db st n)) ∧ π.IsInstance db (E.proof db (run U db st n)) :=
  completeness' hwf hσ hπ


/-- Soundness with definitions (`docs/THEORY.md`, "Definitions", milestone 9): over
the database extended by the rules of the conversion judgment, the closing of the
proof of every entry at the root stands for an MM0 proof — with conversion steps —
of the statement under the answer and the closing. -/
theorem soundness_defs (U : Unification) (L : Language) (db : Database) (hwf : db.WF) (hdefs : db.DefsWF)
    (st : Statement) (hL : L.WF db st) (n : ℕ) :
    ∀ E ∈ (run U (db.withConv L) st n).rootEntries U st,
      (∀ v ∈ (E.proof (db.withConv L) (run U (db.withConv L) st n)).allVars (db.withConv L),
        st.dummies v.ty.sort = true) →
      IsProofD db L.sig
        (st.subst (((E.proof (db.withConv L) (run U (db.withConv L) st n)).closing (db.withConv L)).comp E.sub))
        (((E.proof (db.withConv L) (run U (db.withConv L) st n)).close (db.withConv L)).toD L db) := by
  intro E hE hd
  have hwf' := Database.withConv_WF (L := L) db hwf hdefs
  have hs := run_inv U (db.withConv L) hwf' st n
  have hinv := sptE_inv hs _ 0 hs.root_lt E hE
  have hσ : (((E.proof (db.withConv L) (run U (db.withConv L) st n)).closing (db.withConv L)).comp E.sub).Typed :=
    Subst.Typed.comp (closing_typed _ _) hinv.typed
  exact toD_isProof (hL.subst hσ) hdefs (soundness U (db.withConv L) hwf' st n E hE hd)

end Theory
