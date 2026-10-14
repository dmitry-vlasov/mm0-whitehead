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
14. **Completeness is for the certificates of the `.mmb` format**, which have no
    transitivity (2026-10-13, found while writing the translation). `mm0.mm0` has
    `CTrans`, and with it `CTrans (CSymm (CUnfold f es [y])) (CUnfold f es [y'])`
    converts `B[y]` to `B[y']`: two unfoldings of one occurrence with different
    dummies rename a bound variable. The `.mmb` format cannot express this — its
    conversion proofs are `Refl`, `Sym`, `Cong` and `Unfold` at the head of an
    obligation, with no cut — and neither can the rules, which unfold at the head on
    either side and compare the rest syntactically (`DESIGN.md`, "Unfolding inside a
    variable"). So the model's judgment keeps `CTrans` and soundness is proved for the
    whole of it, while completeness assumes certificates without it (`CTree.NoTrans`),
    which is what any `.mmb` proof has. Whether the engine should also rename dummies
    is a question for the production engine, not the theory.

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
- What the translations assume beyond validity: the language fits the database and
  the statement (`Language.WF`: the judgment sort is none of the file's, no assertion
  or hypothesis is a judgment at its root); every dummy of a definition occurs in its
  value, and the value is of the result's sort (`Def.WF`); the bound variables of the
  statement depend on nothing (`Consts.NameDeps`); and, for an MM0 proof to be
  translated, that it fits the language (`DTree.Fits`): every expression is over the
  file's sorts and terms with their declared types, every conclusion has a provable
  sort, and every certificate is of the `.mmb` format.

### Milestones

8. The model: `Def`, `Database.defs`, `CTree`, `CValid`, `DTree`, `DShape`, `IsProofD`.
   **Reached on 2026-10-13** (`Defs.lean`), with the first variant's proofs embedded
   as MM0 proofs (`PTree.ofP`, `isProofD_ofP`). The rules and the translation of
   milestone 9 are defined (`Rules.lean`: `Language`, `Database.withConv`,
   `Database.ruleAt`, `PTree.toC`, `PTree.toD`), their theorem is next.
9. The extended database (`Database.withConv`), its well-formedness, and the
   translation from proofs over it to MM0 proofs with its theorem (`toD_isProof`);
   `soundness_defs`. **Reached on 2026-10-13** (`ToD.lean`, `Theorems.lean`). The
   rules are looked up by index (`ruleAt`, `mem_all_spec`: what a rule of each kind
   is, by the construction of the list). A valid rule tree whose expression is a
   judgment stands for a valid certificate (`cert_valid`): the arguments of a
   congruence by one lemma over the argument types with the two counters, of
   variables and of positions (`congList_valid`); an unfolding by the instance of
   the definition under the step's substitution, which is that substitution on the
   value (`Def.inst_apply`), its conditions from the step's pairs — apart from every
   argument, and distinct by the pairs of each dummy with every later one
   (`nodup_map_of_laterPairs`). A valid tree whose expression is no judgment stands
   for a valid MM0 proof (`proof_valid`): which steps can occur at which level is
   decided by the sort at the root, a judgment's being the judgment sort, which no
   sort of the file is (`Language.WF`). The conditions of the MM0 proof are among the
   tree's (`conds_toD`) and so are its variables (`proof_vars`, `cert_vars`), the
   latter because every dummy of a definition occurs in its value (`Def.WF`,
   `dummies_used`: a dummy that did not would be a name the proof shows nowhere).
   The extended database is well-formed when the file's assertions and definitions
   are (`withConv_WF`). Then `soundness_defs` is `soundness` over the extended
   database followed by `toD_isProof`, the language fitting the instance of the
   statement since the answer and the closing are typed.
10. The translation from MM0 proofs to proofs over the extended database
    (`ofD_isProof`), with the lemmas of decision 11; `completeness_defs`. **Reached on
    2026-10-13** (`OfD.lean`, `Theorems.lean`; the translation is `DTree.toP`, with
    `CTree.toTree` and `CTree.toTreeR` for a certificate in the two directions). The
    lemmas of decision 11 came out simpler than planned: with transitivity excluded
    (decision 14) there is no composition of rule trees, and symmetry needs no
    swapping of a built tree but a second builder that reads the certificate
    backwards, the two defined together with the children of a congruence. A
    congruence step gets its substitution from an association list over the rule's
    variables (`Subst.ofAssoc`, `Build.congAssoc`), and is strict at the first argument
    where the sides differ (`Build.firstDiff`); when the sides are equal the step is
    reflexivity, and a conversion of an expression to itself is dropped with its step
    (`DTree.toP`). An unfolding step gets the arguments, the dummies and the other side
    (`Build.unfoldAssoc`), its conditions from the distinctness of the dummies, which
    are names and have no dependencies (`Consts.names_of_name`). The validity of the
    built trees (`CTree.toTree_valid` and its three companions, over the shared step
    lemmas `congStep_ok` and `unfoldStep_ok`) comes with the bound on their variables
    needed for the dummies: within the two sides and the certificate. Then
    `DTree.toP_valid` and `DTree.toP_isProof`, and `completeness_defs` is
    `completeness` over the extended database.
11. The converter maps the definitions and the rules; the production engine's
    (def, occurrence) steps get an off switch; the differential test on the files
    with definitions (`defs.mmb`, `peano`, `hol`, `mm0`). **Reached on 2026-10-13.**
    `Convert.lean` gives the model the language of the file (`language`: its sorts
    and which are provable, its terms before the judgment terms, the signature, and
    the production engine's judgment sort), its definitions (`defs`), and the
    database with the rules the file has; and it checks, once per file, that the
    rules the model builds (`Rules.all`) are the file's rule for rule, the pairs in
    any order (`rulesMismatch`), and that every definition is well-formed
    (`defsFaults`, the conditions of `Def.WF`). The production engine runs in the
    test without its (def, occurrence) steps (`Env.convSteps`, decision 12), so that
    the two engines have the same steps. On the fixture with definitions
    (`tests/fixtures/prove/defs.mmb`, 9 definitions, 26 theorems) the model's rules are
    the file's, no definition has a fault, and the two engines agree on every theorem
    for 2 and 3 rounds, with the same nodes — at 3 rounds the proofs go through
    `conv_s`, `unfold'_f` and `refl_s`, which no earlier run could reach without the
    rules on both sides. On the corpus, 2 rounds, with the first 300 assertions of the
    file as the database: every 25th theorem of `peano` (108; 158 definitions), every
    100th of `mm0` (49; 412) and every 200th of `x86` (38; 536) agree, and so does every
    3rd theorem of `hol` (34; 20 definitions) with its whole database; on each file the
    model's rules are the file's and no definition has a fault. The check found one
    difference on the way: the number of the rule's variable for the other side of an
    unfolding, which the production engine takes as the number of the definition's
    binders — the model now does the same, with the largest binder plus one as the
    meaning that its proofs need.

## The production engine (the third variant; designed 2026-10-13)

Decision 3 made the reference engine the object of the theorems and deferred a proof
about the production engine. What the production engine does beyond the reference
engine (`Whitehead/Prove`, "The reference engine" above): it keeps *one proof per key*
at a node, the key being the proof's substitution restricted to the visible variables
with its open conditions (`proofKey`); it carries a proof up with that *restriction*
only (`restrict`, `buildPropProofs`); it judges a condition *settled* and drops it,
or *violated* and drops the proof, as soon as that is decided (`judge`, `openConds`);
it joins a new proof of one child with the proofs of the others *incrementally*, as
they come (`addProof`), through a join index; it finds the assertions by the index
and splits the unifier into the part on the goal and the part on the assertion
(`splitProp`); and it has budgets. The engine lemmas of milestone 5 are the
arguments the first three rest on, stated about the reference engine's SPT sets.

### Two ways

- **A proof about the code.** The engine is `StateT Env BaseIO` over arrays and hash
  maps, with `partial` unification, index walks and proof building, and reads of the
  clock and the memory. A proof about it needs a pure, total core carved out first — a
  rewrite of the engine's core (`Proofs.lean`, `Expand.lean`, `Unify.lean`,
  `Index.lean`, `Prod.lean`, some 1,500 lines) with fuel for every `partial` and the
  lemma libraries of `Std.HashMap` and `Array` for the data — and then the proofs
  about that code. `CLAUDE.md` asks the engine to be a program with `partial` and
  in-place arrays, not a proof library, and its performance is measured against
  mm0-c; the rewrite would be against that grain, and the proofs about imperative
  code several times the size of the first two variants.
- **A proof about the algorithm, and a test of the code against it at every node.**
  A third engine in the theory, the *keyed engine*: the reference engine's SPT sets
  with the production engine's three ideas — the restriction on the way up, one entry
  per key, the conditions judged settled or violated or pending — over the model's
  data (`Theory/Keyed.lean`). Two theorems, by the engine lemmas: every entry of the
  keyed engine at a node is the restriction of an entry of the reference engine with
  the same conditions pending, and every entry of the reference engine has an entry
  of the keyed engine with its key; so the keyed engine's answers at the root are the
  reference engine's, and soundness and completeness carry over. Then the
  differential test compares the production engine with the keyed engine *node by
  node*: after each round, the keys of the proofs at every expression node and every
  assertion node, not the root's answers alone. That tests `addProof`, `restrict`,
  `proofKey`, `judge`, `splitProp` and `buildPropProofs` directly, on the fixtures and
  the corpus, which is how the two faults of the metavariable mode were found. The
  incremental join and the index remain the code's own; the test is what covers them.

### Decisions (2026-10-13)

15. The second way (chosen with the user, see the question of the same day): the
    algorithm proved, the code tested against it at every node. The first way stays
    open for the day the engine's core is rewritten for other reasons.
16. (2026-10-14) The correspondence with conditions is proved for an *oriented*
    unification postulate — of two variables that fit each other the one with the
    larger number is bound — rather than up to a renaming of variables: an oriented
    idempotent unifier is unique, so the keyed engine's substitutions are the
    reference engine's restricted ones exactly, and no renaming arises. The concrete
    unifier is oriented since milestone 15, and the production engine's too; the
    theorems of milestones 1 to 14 keep their general postulate.

### The keyed engine

`Theory/Keyed.lean`: `keyedE U st s fuel i : List KEntry`, by the recursion of `sptE`,
where an entry carries its tree, its substitution *restricted to the visible variables
of its node* (`visible st s i`), and its pending conditions; at an assertion node the
join of `θ_a` with one entry per child (their restricted substitutions), the result
restricted to the parent's visible variables, its conditions judged under the answer —
violated: dropped; settled, that is on a name no node above can replace: dropped as a
condition; pending: kept — and the entries kept one per key, the key being the
restricted substitution with the pending conditions, the first found. The engine's
state, rounds and nodes are the reference engine's (`State.run`): the keyed engine
differs in what it reads off the state, as the production engine's tree differs in
its proofs, not its nodes.

### Milestones

12. The keyed engine, running on the fixture: `Keyed.lean`, `lake exe ref-search
    --keyed`. **Reached on 2026-10-13.** The engine is `keyedE`, the recursion of
    `sptE` over entries of `KEntry` (tree, restricted substitution, pending
    conditions): at an assertion node the join of `θ_a` with the restricted
    substitutions of one entry per child (`anodeK`), the conditions judged under the
    join as the production engine's `judge` judges them (`judgeK`: violated when the
    name occurs; settled when the name is a variable not among the variables of the
    parent's expression under the join nor of the statement, or a constant with no
    variable left in the expression; pending otherwise), the join restricted to the
    parent's visible variables, and one entry per key (`dedupKeys`, the first found,
    the key compared exactly). On the logic fixture at 3 rounds the keyed engine has
    1, 4, 3 and 4 entries at the roots of `a1i`, `mpcom`, `alrimi` and `dummy` where the
    reference engine has 1, 36, 83 and 2,079 — and the production engine 1, 4, 3 and
    4. `diff-test --keyed` compares the production engine's root proofs with the
    keyed engine's entries by their *keys* — the answer with the pending conditions,
    renamed by first occurrence — as sets: which proof is kept per key depends on
    the order of enumeration, and how many entries share a key up to renaming on
    which of two variables a unifier keeps, and both differ between the engines; the
    sets agree on both fixtures at 2 and 3 rounds, with and without metavariables.
13. The keyed engine is sound for the reference engine: every keyed entry at a node has
    a reference entry at the node with the same tree, no condition pending, and the
    same answer on the node's visible variables *up to instance each way*
    (`KeyedCorr.lean`, `keyed_sound_np`; at the root, with `soundness_valid`,
    `keyed_soundness_np` in `Theorems.lean`). **Reached on 2026-10-13 for databases
    without conditions on bound variables** (`Database.NoPairs`: no assertion has
    pairs); the conditions are milestone 16. Two things came out differently from the
    design above. The keyed entry is not the *restriction* of the reference entry: the
    join of the restricted members and the join of the full members are unifiers of
    the same problem up to the fresh variables below, and which of two equal variables
    a unifier keeps is the postulate's choice, so the two answers agree on the visible
    variables up to instance each way (`SameOn`), which for idempotent answers is up to
    a renaming; the key is therefore compared up to renaming, as `diff-test --keyed`
    already does. And the argument is not `spt_restrict` alone: a member's variables
    that are not visible at its child are inside that child's block (`KInv`, `Member`,
    `block_apart`), hence apart from `θ_a` and from the other children's members,
    which is what `joinAll_restrict_*` and `joinAll_sameOn` need; a chain over the
    children (`restrict_chain`, `sameOn_chain`) replaces the members one at a time.
14. The keyed engine is complete for the reference engine: every reference entry at a
    node has a keyed entry at the node with the same answer on the visible variables up
    to instance each way, the one kept for its key (`keyed_complete_np`,
    `dedupKeys_spec`; at the root, with `completeness`, `keyed_completeness_np`).
    **Reached on 2026-10-13 for databases without conditions**, by the same chains run
    the other way. A keyed entry carries no proof of its own: its proof is the
    reference entry's, the same tree under the full answer; the restricted answer does
    not instantiate the nodes below. The production engine keeps at every proof node
    the join made there and composes them down the tree when it extracts a proof
    (`makeProofTree`, `Proofs.lean`), which milestone 15's test and the verifier cover.
15. The structural differential test: `diff-test --nodes` compares, after each round,
    the keys at every node of the production engine's tree with the keyed engine's,
    on the fixtures and the corpus samples; what it finds is fixed or recorded.
    **Reached on 2026-10-13.** The two trees are walked together from the root, an
    assertion node of the production engine matched with the reference state's at the
    same expression node applying the same assertion and their children in order, and
    at every expression node and every assertion node the sets of keys up to renaming
    are compared (`Diff.lean`, `compareNodes`). It found three things, all about
    which of two variables a unifier binds — a choice the theorems leave open and the
    keys up to renaming absorb at the root, but not at the nodes below, where a
    binding made at one node of one engine is made at another node of the other.
    First, the reference engine's unifier bound a metavariable to an assertion's
    renamed variable at the root, so that below the root the metavariable was not in
    play and the production engine's keys, which carry its binding everywhere, had no
    counterpart: the theory's unifier now binds the fresher variable, the one with
    the larger number (`Unify.lean`, `go`; the proofs were untouched but for the
    branch's condition). Second, the production engine did the converse at an inner
    node, binding a metavariable to a fresh variable because the fresh one came later
    in the array of expressions (`unifyStepVar`): it now binds the fresher too, an
    assertion's variable counting as freshest (`fresher`, `Whitehead/Prove/Exp.lean`,
    in its three places). Third, a production fault: a premise with two
    metavariables against a node that has them swapped found no match, the occurs
    check reporting a cycle for a variable to be bound to what is already bound to
    it; `Binds.bind` resolves the chain first, and the proof — the two metavariables
    identified, a legitimate answer that completeness requires — is found. After the
    three changes the keys agree at every node of both fixtures, with no, one and two
    metavariables, at 3 and 2 rounds; the main test suite passes with the two unifier
    tests that encoded the positional choice updated. On the corpus, with the first
    300 assertions as the database and every 25th theorem (`peano`: 108 theorems,
    `mm0`: 195, `x86`: 306) and with the first 100 and every 100th of set.mm (391 of
    478, the rest over the tuple cap), at 2 rounds, the keys agree at every node —
    up to 12,000 nodes compared for one theorem; the `peano` sample with its first
    variable a metavariable agreed on the 21 theorems it reached in 50 minutes.
16. The conditions: milestones 13 and 14 for databases with pairs. **Started on
    2026-10-14.** The design (decision 16) does without a theory of renamings. What
    made one seem necessary: a pending condition mentions variables that are not
    visible at its node, the fresh ones of the blocks below, and for those the two
    engines' answers are related only by which variable a unifier keeps of two it
    makes equal. But both unifiers now keep the older one (milestone 15), and an
    idempotent unifier with that orientation is *unique*: of two such unifiers that
    are instances of each other, each representative the first keeps the second
    would have to bind to an older one and the first then bind that one back, which
    the orientation forbids (`Oriented.lean`, `oriented_unique`). So, for an oriented
    postulate (`Unification.Oriented`, which the concrete unifier has), the join of
    restricted members *equals* the join of the full members on every variable that
    the restriction did not drop (`joinAll_restrict_eq`, the exact form of
    `joinAll_restrict_instance`: the restricted join extended by the dropped bindings
    is an oriented idempotent unifier of the full problem, hence the full join), and
    the keyed engine's substitutions are exactly the reference engine's restricted
    ones, conditions included: every keyed entry has the reference entry with its tree
    whose restricted answer it is and whose conditions it has filtered to the pending
    ones, and conversely. The plan, in order: (a) the settled test: `judgeK` and the
    production `judge` must take the name as still replaceable when it occurs in the
    *image* of a visible variable under the answer, the metavariables' values
    included, not only when it occurs in the expression's image or is a variable of
    the statement — a name inside a metavariable's value can be identified above with
    a name of the condition's expression (found by writing this proof; the fixtures
    and samples did not show it); (b) `Oriented` and the uniqueness theorem, and the
    concrete unifier oriented; (c) `joinAll_restrict_eq` and `joinAll_key_eq`; (d)
    the exact correspondence with conditions, by the induction of milestones 13 and
    14 with equalities in place of `SameOn`, the settled conditions preserved above by
    `joinAll_mentions` since no member above mentions their name; (e) the root
    theorems and the differential test rerun.

## Questions

Asked on 2026-10-13: which of the two ways of "The production engine"; the second was
chosen (decision 15).

Answered on 2026-10-13: definitions are excluded (decision 6); metavariables stay
(decision 7); closing is a separate step, and trivial where the sorts allow dummies
(decision 8). The earlier form of the question had it wrong: MM0 does allow dummies of
every sort that is neither `strict` nor `free`, so a variable left for an expression of
such a sort becomes a dummy like a variable left for a bound variable.

Open: the forward direction restricts a fact's substitution to its pattern
(`Forward.lean`) without the task's metavariables; whether that matters waits for the
forward direction's own model (decision 4).
