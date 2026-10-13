# The verification of the engine

Started on 2026-10-13, as an interruption of phase 4. The goal: a proof of the soundness
and the completeness of the prover's engine for MM0. This file is the plan and the
record of the decisions; the formal development is the Lake package `theory/`.

## Decisions (2026-10-13)

1. The deductive system is MM0. The engine over a fragment of Lean (the ARGO talk's
   "Ramsey", the draft's `D_syn`) is for the future.
2. The theory package may depend on Mathlib. The main package stays without it
   (`CLAUDE.md`); the theory package depends on the main package, not the other way.
3. The object of the theorems is a *reference engine*: a pure, executable Lean version of
   the search as the papers define it. The production engine (`Whitehead/Prove`) is
   tested against it; a proof about the production engine itself is deferred.
4. Backward search only. The forward direction is for later.
5. Soundness as well as completeness; generality comes with them.
6. (2026-10-13, later) Definitions are excluded from the first variant. They are to be
   added afterwards with their original semantics — MM0's conversion judgment — rather
   than only as assertions. The converter leaves the conversion rules out.
8. (2026-10-13, later) Closing — giving the variables a proof leaves to a value — is a
   step of its own after the search (`PTree.close`, with its own theorem
   `close_isProof`), as the production engine has it at emission. Every variable left
   becomes a dummy of its sort, which MM0 allows in a theorem for every sort that is
   neither `strict` nor `free` (`mm0.md`: "any number of additional dummy variables of
   any desired sorts"; a dummy is a bound variable, and a bound variable is an
   expression of its sort). In the set.mm translation `wff` and `class` are neither, so
   the closing is this trivial one. What is not in the model: the sorts that allow no
   dummies, where the production engine tries a term without arguments or a variable
   of the theorem; and MM0's limit of 55 bound variables per theorem, which
   `mergeNames` meets by merging leftover names that no condition keeps apart.
7. (2026-10-13, later) The statement may have metavariables (free variables are
   constants, metavariables are variables of the tree, as in `Db.task`). They do not
   complicate the theory: the root is an expression node like any other, and every
   theorem is about instances of the statement — what an entry proves is the statement
   under its answer. A statement without metavariables is the case where every
   instance is the statement itself.

## The documents

- D. Vlasov, *Proof Search Algorithm in Pure Logical Framework* (2017;
  `russell-flow/docs/proof_search_algo.pdf`): the proof variant tree (PVT), the
  substitution proof trees (SPT), the unification of substitutions, and the three
  theorems — correctness (1), generality (2), completeness (3) — for a pure logical
  framework. It sets aside the disjoint-variable restrictions and the algorithm for
  unifying substitutions.
- D. Vlasov, *Substitution-Join Proof Search in Lean: Soundness, Generality and
  Completeness Modulo Oracles* (draft, October 2026): the same over an abstract
  *unification structure* — a term language with scoped metavariables (Definition
  2.1), a normal form (2.3), a unification class with unique most general unifiers
  (Postulate 2.5) and the join of substitutions through their equational form
  (Definition 2.6, Lemma 2.7) — and a *contextual deductive system* (3.3); proof trees,
  variants and their equation systems (3.4–3.7); the PVT (4.1) and the SPT sets (4.2);
  the SPT lemma (4.3), the one place where the per-subtree joins meet the global
  unifier; the theorems (4.4–4.6); sharing and subsumption (4.7, 4.8); oracles with
  obligations (Section 6). Its "write out" markers are at Lemma 3.5, Lemma 4.3 and
  Theorem 6.6.
- The talk *From Russell to Lean 4* (ARGO, 2026-10-08): the roadmap, "formalize
  completeness first — for Whitehead".
- `DESIGN.md`, "MM0 as a deductive system of the paper" and "Where MM0 differs: bound
  variables": the instance, and the rule for the conditions on bound variables — a
  tree may be discarded only when a condition is violated for every instantiation.

## The model

What is formalized, in the draft's terms, specialized to MM0.

- **Terms.** Sorts; a type is a sort with a bit for "names only" (`Ty` of `Exp.lean`): a
  bound binder `{x: s}` is a variable of the type of names of `s`, a regular binder of
  the type of `s`, and an argument position declared with braces takes names. A term
  symbol has argument types and a result sort. An expression is a variable or an
  application, well-typed. The variables of the statement being proved are constants
  (applications without arguments), each with the bound variables it is declared to
  depend on; the statement's bound variables are constants of a name type.
- **Substitutions.** Finite support, typed: a variable of type `t` gets an expression
  of a type that fits `t` (the same sort; a name type only names). Application,
  composition, instance (`θ ≼ σ`), idempotence. Normal form: the identity.
- **Unification** as the draft's Postulate 2.5, a structure: a class of problems closed
  under union and instantiation, a most general unifier of every solvable problem,
  unique up to renaming, with the set of solutions its instances; decidable. First the
  theorems are proved relative to it; then it is discharged for sorted first-order
  terms by a unifier of the package with its proof (milestone 7, done). The join of
  substitutions is defined through it (Definition 2.6).
- **Conditions.** For an assertion, the pairs `D(A)` of `DESIGN.md`: `(x, v)` with `x`
  bound, `v` another binder, unless `v` is regular and declares `x`. A substitution
  *satisfies* the pair when the name `θ(x)` does not occur in `θ(v)`, where "occurs"
  counts, for a constant of the statement, its declared dependencies. These are the
  draft's admissibility, as occurrence constraints between substituted variables rather
  than scopes of rigid variables.
- **The deductive system.** Assertions (binders, hypotheses, conclusion, pairs) in a
  database; the hypotheses of the statement as facts (premise-free local assertions);
  no structural rules. No definitions in the first variant (decision 6).
- **Proofs.** Proof trees as in the paper: e-nodes with expressions, a-nodes with
  `(a, θ)`, leaves e-nodes that are hypotheses; valid when every transition is the
  instance of its assertion under a typed substitution that satisfies the pairs. A
  proof of the statement is a valid tree with the statement at the root, closed except
  for *dummies*: variables of a name type, distinct from each other and from the
  statement's names, which become the dummies of the MM0 proof.

One correction to the draft's wording of Definition 4.2, found while writing the
engine: the entry of an assertion node must join the children's answers *with the
node's own unifier* `θ_a`, or the metavariables of the parent that `θ_a` binds are lost
from the answer (a goal `?g` proved by `¬¬x' / x'`: the child's answer binds `x'`, and
only `θ_a` says `?g ↦ ¬¬x'`). The 2017 paper's correctness proof has the witness
`θ_0 ∘ η`, and Russell's `ruAddProof` composes `prop.sub` with the join. Recorded in
`Search.lean`.

## The reference engine

`Theory/Search.lean`: the PVT and the SPT sets of Definitions 4.1 and 4.2, computed
round by round, breadth first — the fair expansion of the completeness theorem. An
e-node is expanded against every assertion whose conclusion unifies with it, the
assertion's variables renamed fresh; the children are the hypotheses under the unifier.
An SPT entry is a tree of nodes with its answer substitution; a leaf entry is a
hypothesis matched by unification; an a-node entry is the join of one entry per child;
an e-node has the entries of its a-children. The conditions of every a-node on the path
travel with the entry under its substitution; an entry is dropped only when a condition
is violated under every instantiation (`DESIGN.md`). Every entry is kept: no key, no
restriction, no limit but the number of rounds. The engine is a pure function of the
database, the statement and the number of rounds, and it runs.

What the production engine does beyond this — the restriction of substitutions on the
way up (change 5), one entry per key, conditions settled and forgotten, the forward
direction, the index and the product unifier, the limits — is not in the reference
engine. The first three are stated as lemmas about the reference engine's SPT sets
(milestone 5), since they are the arguments the production engine rests on.

## The theorems

For a database, a statement and the reference engine after `n` rounds (`Theorems.lean`;
"the statement" below means an instance of it under a substitution of its
metavariables, decision 7):

- **Soundness** (paper's Theorem 1, draft's 4.4): the proof of every entry at the root
  is valid for the statement under the answer and proves its conclusion; and it has an
  instance that is a proof of the statement — the variables it leaves open given
  distinct fresh names.
- **Generality** (Theorem 2, 4.5): the proof of a root entry is more general than any
  proof of the statement congruent to it.
- **Completeness** (Theorem 3, 4.6): for every proof of the statement there is a number
  of rounds after which the root has an entry of which the proof is an instance.
- **The engine lemmas**: an entry's join depends only on its substitution restricted to
  the variables of its node's expression (restriction); two entries with the same
  restricted substitution and open conditions are interchangeable above (key); a
  condition on a name that no node above can replace holds or fails for good (settled).

Soundness here is validity in the model. That the model's valid proofs are the proofs
`mm0.lean` accepts is the verifier's own correctness, a separate track (`CLAUDE.md`,
phase 2: "structurally close to the MM0 semantics formalization").

## The link to the production engine

A converter from `Db` (the prover's database of a `.mmb` file) to the model's
database, and a differential test: on the fixtures and on samples of the corpus, the
production engine with `breadthFirst`, no limit but the rounds and no forward front,
against the reference engine with the same number of rounds. Each proof the production
engine has at the root must be an instance of a reference entry, and each reference
entry's key must be among the production engine's. This is the same method as the
unifier's test against its reference unifier.

## Milestones

1. The package: `theory/` with Mathlib, depending on the main package; the model
   (`Term`, `Subst`, `Unification`, `Deduction`), the reference engine (`Search`), and
   the three theorems stated, their proofs pending. Everything type-checks and the
   engine runs on the logic fixture. **Reached on 2026-10-13**: `cd theory && lake
   build` (Mathlib v4.34.1, our toolchain; `lake exe cache get` for its oleans) builds
   the model, the engine, the four theorem statements (`sorry`), and a first-order
   unifier (`Unify`) whose postulate is carried with `sorry` until milestone 7.
   `lake exe ref-search ../tests/fixtures/prove/logic.mmb a1i 2` finds `(ax_mp h ax_1)`
   as the production engine does; `mpcom` in 2 rounds gives `(com12 id)`, in 3 rounds
   36 proofs at the root from 369 entries; `alrimi`, with conditions on a bound
   variable, 1 proof in 2 rounds and 83 in 3. A converter (`Convert`) maps the
   production database and task to the model.
2. Substitutions and proof trees: composition, instance, the monotonicity lemma (3.5).
   **Reached on 2026-10-13**: `Subst.lean` has composition, typing (`ty_apply`,
   `Typed.comp`), and what a substitution does to the variables and constants of an
   expression (`vars_apply`, `consts_apply`); `Deduction.lean` has the monotonicity
   lemma `Shape.subst`, and how the conditions and the expressions of a tree change
   under a substitution; `Closing.lean` proves `close_isProof`: the closing of a valid
   tree is a proof of the statement — a condition keeps holding under fresh distinct
   dummies (`holds_closing`), and in a well-formed database every condition's name is
   a name (`conds_name`). So `soundness` rests on `soundness_valid` alone. The closing
   covers every variable of a tree, in its expressions and in its conditions
   (`allVars`), and names the dummies by an injective code of the variable.
3. The SPT lemma (4.3) for the backward engine: every entry's substitution is the most
   general unifier of its variant's equation system, and conversely. **The soundness
   half reached on 2026-10-13** (`Spt.lean`, `Preserve.lean`): an answer solves the
   equational form of a unifier exactly when it absorbs it (`θ ∘ σ = θ`), and the join
   of a list absorbs each member; the invariants — the tree sits in the graph, the
   answer absorbs every unifier on it, the carried conditions are the tree's under the
   answer and hold — give a valid proof (`valid_of_inv`), and the engine keeps them
   (`run_inv`, `sptE_inv`). The engine was rewritten as folds and recursions for this,
   with the SPT sets a recursive function of the depth. The converse, that the answer
   is *most general*, is what generality and completeness need and is still to do.
4. Soundness, then generality and completeness from the SPT lemma. **All three reached
   on 2026-10-13**, relative to the unification postulate. Soundness: `Spt.lean`,
   `Preserve.lean`. Generality (`Generality.lean`): a proof congruent to an entry's
   tree gives one substitution on the whole state (`build`): the instance's below the
   fresh variables, and at the renamed binders of each node of the tree what the
   proof's step there gives them — well defined because a tree never visits a node
   twice (`anodes_nodup`, through the chain of nodes above a node, `chain`); it absorbs
   the tree and the proof is the tree's proof under it (`sim`); an entry's answer is
   most general among what absorbs its tree (`entry_mostGeneral`); so the proof is an
   instance. Completeness (`Completeness.lean`): the model records every attempt with
   the base it used, so that an expanded node is known to have tried every assertion
   (`tried_of_lt`), and an assertion node is known to have been made in the round after
   its parent appeared (`anode_round`); the proof's variant is built by following the
   proof into the graph (`treeOf`), each needed node shown to exist because a
   substitution solving its equation exists (`override`, `treeOf_at`); the entry for
   that variant exists at the depth the tree needs (`entry_exists`, with the join most
   general and the conditions kept under the answer, `holds_of_instance`), and the
   depth is within the state (`fuel_le`); generality's argument then gives the
   instance. To make instances equalities, the model changed along the way: leaves
   carry their hypothesis, step substitutions stay on the binders, bases follow node
   numbers, typed substitutions give names to name types, and the postulate says a
   unifier mentions no variable outside its problem.
5. The engine lemmas: restriction, key, settled.
6. The differential test.
7. The unification postulate discharged for sorted first-order terms. **Reached on
   2026-10-13** (`Unify.lean`): `Unify.postulate : Unification` with no `sorry`. The
   unifier is Robinson's, one equation at a time, binding a variable to the other side
   (`bind`, with the binding applied to the equations left, `bindIn`) when the types
   fit, the variable does not occur, and a name type gets a name; it recurses on the
   pair (number of variables, size of the problem), which a binding lowers in the
   first component and dropping or decomposing an equation in the second. The proof
   carries an invariant: the substitution so far is typed, its images avoid its
   domain, its domain is apart from the equations left, and everything stays within
   the variables of the original problem. Soundness (`go_sound`): the result solves
   the equations, absorbs the substitution so far, and the invariant at the end gives
   typing, idempotence (`idem_of_sep`), and the domain and range conditions.
   Completeness (`go_complete`): a typed solution absorbing the substitution so far
   solves the equations after a binding and absorbs the new substitution
   (`bind_complete`), and the failing branches contradict such a solution — the
   types by `Typed`, the occurs check by size (`size_lt_of_mem_vars_app`), the name
   condition by `IsName`; so the result exists and the solution is its instance. The
   theorems of milestone 4 are now unconditional.

Later: the forward direction; the production engine; the verifier against `mm0.lean`;
the fragment of Lean.

## Questions

Answered on 2026-10-13: definitions are excluded (decision 6); metavariables stay
(decision 7); closing is a separate step, and trivial where the sorts allow dummies
(decision 8). The earlier form of the question had it wrong: MM0 does allow dummies of
every sort that is neither `strict` nor `free`, so a variable left for an expression of
such a sort becomes a dummy like a variable left for a bound variable. Nothing is open.
