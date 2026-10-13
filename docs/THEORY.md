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

`lake exe diff-test <file.mmb> <rounds> [--from A] [--to B] [--every K] [--meta I,J]
[--max-tuples N] [--max-nodes N] [--assertions K] [--verbose] [--dump]`
(`theory/Diff.lean`) runs it.
The production engine is driven round by round there, since its search stops at the
first proof accepted: the root is expanded, then each round expands every assertion
node made before it. The production engine makes the children of an assertion node
when it expands the node, matches them with the premises then, and expands them
against the assertions; so after `n` such rounds its proofs at the root use the
assertion nodes of depth up to `n` and hypotheses at expression nodes of depth up to
`n`: the reference engine's entries after `n` rounds. The assertion nodes of depth
`n + 1` are not expanded within the `n` rounds and give no proof, and on a corpus file
they are the bulk of the work — a premise that is a bare variable unifies with
thousands of assertions — so the last round sees no assertions and makes none of them;
the two engines then have the same nodes. The products of such premises are beyond
memory in either engine, so a theorem is left out, reported and not counted as a
disagreement, when the joins of either engine would visit more tuples of proofs than
`--max-tuples` (1,000,000 unless given) — the production engine's count of the sizes
of the products it joins, and the same sum over the reference engine's enumeration,
checked before each product is built (`sptEC`, the recursion of `sptE` with the
guard) — or the production engine makes more assertion nodes than `--max-nodes`
(2,000,000). The tuples of a theorem late in a file grow with the square of the
assertions before it — on set.mm they pass a billion from the 900th theorem on —
past what the reference engine can enumerate; `--assertions K` gives every theorem
the first `K` assertions of the file as its database instead (the task's limit, which
both engines follow), so that the statement of every theorem of a file can be tested.
The production engine runs first, being the quicker; the reference engine's time is
measured around a call that is not inlined, since a pure value is otherwise computed
where it is first used.
A proof is compared by its *shape* — the assertions of its steps and the hypotheses
at its leaves — and its *answer* — the goal and the metavariables under its
substitution, variables renamed by first occurrence, since a most general unifier is
unique up to renaming only and the two engines name fresh variables differently.
Proofs with a conversion step have no counterpart in the reference engine (decision 6)
and are left out.

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
5. The engine lemmas: restriction, key, settled. **Reached on 2026-10-13**
   (`Engine.lean`). What a substitution *mentions* is what it moves and what it puts
   there; a join mentions only what its members mention (`joinAll_mentions`). The
   visible variables of an expression node are those of its expression and of the
   statement (`visible`); what an entry moves outside them lies in the blocks of the
   assertion nodes of its tree (`entry_mentions`), which come after the node
   (`anode_lt_of_child`, by one more invariant of the state: nodes are made in order)
   and are apart from the trees of the other children (`sibling_trees_disjoint`), so
   no other member of the join at the node mentions them (`spt_join_hyps`). Then:
   *restriction* (`spt_restrict`, from `joinAll_restrict_exists` and
   `joinAll_restrict_instance`): the join exists with the entry's substitution
   restricted to the visible variables exactly when with the whole one, and the two
   answers are instances of each other on the visible variables — "the same up to
   renaming", which is all the postulate fixes; *key* (`spt_key`): two entries of a
   child with the same restriction give joins that exist together, agree on the
   visible variables up to instance each way, and judge every condition on visible
   variables alike (`holds_of_agree`, with the answer itself as the typed witness of
   the instance); *settled* (`spt_settled`, from `settled` and `settled_joinAll`): a
   condition whose name is a variable below the node that the entry does not mention
   holds under the join exactly when it holds already, and the join does not mention
   the variable either. A finding on the way: the production engine's `restrict` kept
   the variables of the node's expression only, not the statement's metavariables,
   which a premise can bind at a leaf without their occurring in the expressions
   between the leaf and the root — two leaves could then bind one differently and the
   join above would not notice. It now keeps the task's metavariables too
   (`Proofs.lean`, backward direction; the forward direction is left as it is,
   decision 4).
6. The differential test. **Reached on 2026-10-13** (`theory/Diff.lean`). On the logic
   fixture the two engines agree on every theorem for 2 and 3 rounds, with the proofs
   of the production engine among the reference entries and every reference answer
   among the production engine's (for 3 rounds the reference engine has up to 2,079
   entries at a root where the production engine keeps 4, one per key); and with
   binder 0, 1 or 2 of each theorem as a metavariable, where the answers are not
   trivial. The test found two faults of the production engine's metavariable mode,
   both fixed: the values of the metavariables were read from the bindings of all the
   steps (`metaValues`), which could pick up a value from a step below that the steps
   above bound further — they are now read from the root proof's substitution, which
   carries them since milestone 5; and `addProof` composed the node's unifier with the
   children's join (`ruCompose(prop.sub, unif.sub)`), which is the join only when
   nothing below binds what the unifier binds — true of the goal's variables, not of
   a metavariable that a premise binds at a leaf: a proof of `com12` with `ps` a
   metavariable bound it to `ph -> ?x` at the node and to `?x` at the leaf, and the
   composition kept the first. With metavariables the two are now unified.
   On the corpus (2 rounds), with all the assertions before a theorem as its database:
   of every 25th theorem of `peano`, the first 28 of the sample agree (17 with proofs
   at the root; two proofs with a conversion step left out) and from `eqthed` on, past
   the 700th theorem, every one is over the tuple cap — the product at a node grows
   with the square of the assertions that a bare-variable premise unifies with; of
   every 100th of the first 1,500 theorems of set.mm, `T0` to `T400` agree, `T500`
   agrees with the cap raised to 30 million tuples (the reference engine visits 5.0
   million, 71 s, 0.9 GB), and from `T600` the reference engine's enumeration passes
   30 million, while the production engine's products pass a billion from `T900` and
   it joins them through its index. With the first 300 assertions of the file as every
   theorem's database: all 108 of the `peano` sample agree (11 with proofs at the
   root), all 49 of every 100th theorem of `mm0`, all 38 of every 200th of `x86`; of
   every 500th theorem of set.mm (95), 50 agree and 45 are over the tuple cap, and with
   the first 100 assertions 77 agree and 18 are over — nearly all agreeing that there
   is no proof, the database holding little that a later statement can use (2 and 1
   with proofs at the root). No disagreement anywhere; the per-theorem lines are what
   `diff-test` prints. Three rounds are beyond the corpus: with all the assertions
   before a theorem every one of every 100th theorem of `peano` is over the tuple cap,
   and with the first 60 assertions the production engine did not finish the first
   theorem of the sample in half an hour — the driver gives it no work budget, and the
   products of the third round are products of products. The corpus needed three changes to the test, all made the same
   day: the production engine's last round makes no assertion nodes (the next level,
   unexpanded, gives no proof, and on a corpus file it was a million nodes and minutes
   per theorem; the two engines now have the same nodes), the two caps and
   `--assertions`, and the reference engine's time measured around a call that is not
   inlined (it read 0 ms before). The first corpus runs, without caps, took the memory
   of the machine. A run with the cap at 30 million found a crash of the production
   engine: `tuplesUpTo` (`Prod.lean`), the enumeration of the tuples of a join one at
   a time, was two nested `while` loops in `Id`, which the compiler made a closure call
   deeper per tuple, and `T1200` of set.mm overflowed the stack; it is now recursion
   on a count, which compiles to a loop, and the same run goes on to the memory the
   budget asks for (13 GB).
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

## Definitions (the second variant; started 2026-10-13)

Decision 6 deferred definitions "with their original semantics — MM0's conversion
judgment — rather than only as assertions". The second variant adds them so.

### Decisions (2026-10-13)

9. **The judgment is the primary specification's.** `examples/mm0.mm0` checks a
   conversion by a certificate (`CExpr`): `CRefl`, `CSymm`, `CTrans`, `CCong` with one
   certificate per argument, and `CUnfold f es zs`, a leaf, `f(es) = B[xs := es, ys :=
   zs]` for `def f (xs) {.ys} = B`, each `z` a bound variable of the context that occurs
   in no argument (`VerifyConvUnfold`). `mm0.lean` has the same judgment without
   transitivity, a `.mmb` `Conv` being a chain of its `conv` proof steps; the model
   follows `mm0.mm0`, with its `VConv c p : B` from `c : A = B` and `p : A`. Two
   additions from the verifiers: the dummies of one unfolding are distinct from each
   other (`MMB-NOTES.md`, section 9, point 4: `E. y E. z ~ y = z` could otherwise be
   unfolded to `E. y E. y ~ y = y`), and at an argument that takes names both sides of
   a congruence are the same name (`mm0.mm0` asks both to be bound variables, and
   two bound variables have no certificate between them but through themselves; the
   theory takes the consequence as the rule rather than prove it about normal forms).
10. **The engine is unchanged; the database grows.** The reference engine searches, as
    the production engine does inside a variable, with MM0's judgment as assertions
    (`DESIGN.md`, "Unfolding inside a variable"): terms `≡_s` and `≡'_s` of a judgment
    sort, and the rules `conv_s`, `refl_s`, `cong_t`, `cong'_t_i`, `unfold_f`,
    `unfold'_f`, `fold_f`, `fold'_f`, exactly the production engine's `convRules` so
    that the differential test compares like with like. The theorems of the first
    variant hold for this database as for any other; what definitions add is the
    link between proofs over it and MM0's own proofs.
11. **Two translations make the link.** From a proof over the extended database to an
    MM0 proof: a `conv_s` step becomes a `VConv`, its `≡'` subtree a certificate
    (`refl_s` to `CRefl`, `cong_t` to `CCong`, `unfold_f` to `CTrans (CUnfold ..)`,
    `fold_f` to `CTrans .. (CSymm (CUnfold ..))`). From an MM0 proof to one over the
    extended database: a certificate becomes a rule tree — `CSymm` pushed to the
    leaves, where it swaps `unfold` and `fold`; `CTrans` by a lemma that composes rule
    trees (an unfolding on the left of a rule tree is undone by induction on the
    tree, with congruence of substitution for the `cong` case); then the tree is
    primed along a path to one of its unfoldings, and a certificate with no
    unfolding, which converts an expression to itself, is dropped with its `VConv`.
12. **The (def, occurrence) steps** of the production engine (`convRule`) are derived
    rules of the extended system — `C[B] ⊢ C[f(xs)]` by `conv_s` over `cong'` along
    `C` to `unfold'_f` — so soundness covers them, and completeness is not affected
    by their presence. In the differential test they are switched off (an option of
    the production engine), so that the two engines have the same steps per round.
13. **Generality** stays within the extended system (a proof congruent to an entry
    uses the same rules); the two theorems restated for MM0 are soundness and
    completeness.

### The model (`Theory/Defs.lean`)

- A definition: the term, its result type, its arguments and dummies as variables,
  and its value over them (`Def`); well-formed when the value is over them, the
  dummies are name-typed, and all are distinct. A database carries its definitions
  beside its assertions (`Database.defs`); the engine never reads them.
- A certificate (`CTree`) as in decision 9, and its validity `CValid db sig c k e₁ e₂`,
  "`k` converts `e₁` to `e₂`", over the signature for the typing of a congruence and
  the constants of the statement for the names an argument has.
- An MM0 proof (`DTree`): a hypothesis, an assertion step, or a conversion `conv e k t`
  proving `e` from `t` by `k : t.expr = e`; its shape, conditions, variables; a proof of
  the statement (`IsProofD`) as `IsProof` with conversions.

### Milestones

8. The model: `Def`, `Database.defs`, `CTree`, `CValid`, `DTree`, `DShape`, `IsProofD`.
   **Reached on 2026-10-13** (`Defs.lean`), with the first variant's proofs embedded
   as MM0 proofs (`PTree.ofP`, `isProofD_ofP`). The rules and the translation of
   milestone 9 are defined (`Rules.lean`: `Language`, `Database.withConv`,
   `Database.ruleAt`, `PTree.toC`, `PTree.toD`), their theorem is next.
9. The extended database (`Database.withConv`), its well-formedness, and the
   translation from proofs over it to MM0 proofs with its theorem (`toD_isProof`);
   `soundness_defs`.
10. The translation from MM0 proofs to proofs over the extended database
    (`ofD_isProof`), with the lemmas of decision 11; `completeness_defs`.
11. The converter maps the definitions and the rules; the production engine's
    (def, occurrence) steps get an off switch; the differential test on the files
    with definitions (`defs.mmb`, `peano`, `hol`, `mm0`).

## Questions

Answered on 2026-10-13: definitions are excluded (decision 6); metavariables stay
(decision 7); closing is a separate step, and trivial where the sorts allow dummies
(decision 8). The earlier form of the question had it wrong: MM0 does allow dummies of
every sort that is neither `strict` nor `free`, so a variable left for an expression of
such a sort becomes a dummy like a variable left for a bound variable.

Open: the forward direction restricts a fact's substitution to its pattern
(`Forward.lean`) without the task's metavariables; whether that matters waits for the
forward direction's own model (decision 4).
