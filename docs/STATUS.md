# Status

Last updated: 2026-10-16.

## Phase

**Phase 1 — readers**: done; the acceptance tests pass (report below).
**Phase 2 — independent verifier**: done; the acceptance tests pass (report below).
**Phase 3 — prover**: done; accepted on 2026-10-13, with both acceptance tests passed
(report below). Two known gaps are carried under "Next steps": shared conversions in
the replay reader, and the checking of a proof found for a task with metavariables.
**Phase 4 — pattern mining and ranking**: started on 2026-10-13, and paused the same
day. The design, with its questions, is in `DESIGN.md` ("Phase 4"); the first tool, the
chain miner (`prove chains`), is built, and its numbers are below.
**Housekeeping, 2026-10-16**: both packages build with no warnings, and `lake build`
now builds every library and executable of a package (`ref-search` had not compiled
since milestone 12 without this being seen); the docs were checked against the code.
A verifier fault was found on the way: a `Dummy` of a sort ≥ 128 was taken for its low
7 bits and a wrong proof accepted (`MMB-NOTES.md`, section 9, point 22); fixed, with two
fixtures.
**The verification of the engine** (`THEORY.md`): started on 2026-10-13, before phase 4
goes on — a reference engine in Lean with Mathlib, in the package `theory/`, and the
proofs of its soundness and completeness for MM0, backward search; the production
engine to be tested against it. Reached the same day: the model, the engine and the
theorem statements type-check, the engine runs on the logic fixture with the
production engine's answers, and **soundness, generality and completeness are proved**
for the reference engine (`THEORY.md`, milestones 1–4), with the unification postulate
discharged for a first-order unifier (milestone 7), and the engine lemmas that the
production engine's restriction, key and settled conditions rest on proved about the
reference engine's SPT sets (milestone 5). `cd theory && lake build` has no `sorry`.
Milestone 5 found that the production engine's restriction dropped the bindings of the
task's metavariables made at leaves; fixed in `Proofs.lean`. The differential test
(milestone 6, `theory/Diff.lean`, `lake exe diff-test`) agrees on the logic fixture for
2 and 3 rounds, with and without metavariables, after two more fixes of the
metavariable mode (`metaValues`, and the join of the node's unifier with the children's
in `addProof`); and on the corpus: with the first 300 assertions of a file as the
database, every sampled theorem of `peano`, `mm0` and `x86` agrees, and of set.mm 50
of 95 (77 with the first 100), the rest over the test's tuple cap; with all the
assertions before a theorem, the early theorems of `peano` and set.mm agree and the
later ones are beyond the reference engine's enumeration, which builds every tuple of
a join (`THEORY.md`, milestone 6). No disagreement. All seven milestones of the first
variant are reached. **The second variant, definitions** (`THEORY.md`,
"Definitions"): started and reached its milestones 8 to 10 the same day — the model
of MM0's conversion judgment and of proofs with conversion steps (`Defs.lean`); the
judgment as assertions, exactly the production engine's rules, over which the engine
runs unchanged (`Rules.lean`); soundness, by translating a proof over the extended
database into an MM0 proof (`ToD.lean`, `soundness_defs`); completeness, by
translating an MM0 proof whose certificates are those of the `.mmb` format into a
proof over the extended database (`OfD.lean`, `completeness_defs`). A finding on the
way (decision 14): the primary specification's certificates have transitivity, with
which two unfoldings rename a dummy, which no `.mmb` proof can express. Milestone 11,
the converter and the differential test on the files with definitions, reached the
same day: the model's rules are the file's, rule for rule, on `defs.mmb`, `peano`,
`hol`, `mm0` and `x86`, and the two engines agree on every sampled theorem of each,
with the production engine's (def, occurrence) steps off (`Env.convSteps`). All
eleven milestones are reached. **The third variant, the production engine**
(`THEORY.md`, "The production engine"; decision 15: the algorithm proved, the code
tested node by node): the keyed engine — the reference engine's SPT sets with the
production engine's restriction on the way up, one entry per key and conditions judged
early (`Keyed.lean`, milestone 12) — matches the production engine's root keys up to
renaming on the fixtures and the corpus samples (`diff-test --keyed`); and it is sound
and complete for the reference engine, node by node, for databases without conditions
on bound variables (`KeyedCorr.lean`, `keyed_sound_np`, `keyed_complete_np`;
`Theorems.lean`, `keyed_soundness_np`, `keyed_completeness_np`; milestones 13 and 14),
the answers agreeing on the visible variables up to instance each way rather than
exactly. The structural differential test (`diff-test --nodes`, milestone 15) compares
the keys at every node of the production engine's tree with the keyed engine's; it
found that the two unifiers oriented a binding between a metavariable and a fresh
variable differently — both now bind the fresher variable — and a production fault
in premise matching with two metavariables swapped (`Binds.bind`), fixed; the keys
agree at every node of both fixtures in every metavariable mode, and of the corpus
samples of `peano`, `mm0`, `x86` and set.mm at 2 rounds. The conditions (milestone 16,
reached 2026-10-14): for an oriented unification postulate — of two variables that fit
each other the one with the larger number is bound, as both engines' unifiers do — an
idempotent unifier is unique (`Oriented.lean`), so the keyed engine's substitutions are
the reference engine's restricted ones exactly and its pending conditions the
reference entry's filtered (`KeyedExact.lean`, `keyed_sound_ex`, `keyed_complete_ex`;
`Theorems.lean`, `keyed_soundness`, `keyed_completeness`, and the two for the concrete
unifier). Found on the way and fixed in both engines: the settled test of a condition
ignored the images of the metavariables, where a name a node above can still replace
may sit. All sixteen milestones are reached; `cd theory && lake build` has no `sorry`.
**The verification of the verifier** (`docs/VERIFIER-THEORY.md`, started 2026-10-14):
the MM0 semantics of `mm0-lean/mm0/mm0.lean` ported to Lean 4 (`theory/Spec/Mm0.lean`,
with four deviations recorded: `conv'.trans`, the corrections of `safe_subst` and
of `sexpr.free'` to `mm0.mm0`'s text, and that of `env.extend.defn_def`, V6), the stack machine of `.mmb` files as relations
(`theory/Verifier/Machine.lean`, `mm0b.lean` completed), and its soundness for the
logic proved: a proof file the machine accepts declares an environment all of whose
theorems are proved (`file_sound`, milestone V3). An executable reference verifier
is proved sound for the machine (`checkFile_correct`, V4: a `true` from it is
`env.proof'` of the semantics), and agrees with the fast verifier statement by
statement on every fixture, every corpus file and 24,168 mutants (`lake exe
verify-diff`, V5); the test found a modelling error in the machine's `Hyp` and a
fault in the conversion, both fixed. The match with the specification is proved the
same way (`spec_proved`, V6: a file accepted and matched proves the specification,
`env.proof`), and agrees with `matchSpec` on every corpus pair and 652 mutants. And
the proof file's environment is well-formed (`file_valid`, V3b), so that a file
accepted and matched gives `mm0.mm0`'s `ValidEnv` of the specification but for the
specification's own well-formedness, which the front end establishes (`spec_valid`).
The prover's output is certified by the verified checker (`lake exe certify`,
`scripts/prove-certified.sh`): the replays of peano and of 2,000 set.mm theorems and
the search on the logic fixture are certified against their specifications.
All milestones of the verifier's verification are reached; `cd theory && lake build`
has no `sorry`. Trusted: Lean's kernel, the port of the semantics (four deviations,
recorded), the `.mm0` front end, the byte reader, and the two conversions.

### Phase 1 acceptance

> All example `.mm0`/`.mmb` pairs in the MM0 repository, and the set.mm translation,
> parse/decode without error and round-trip through `dump` consistently.

- Every `.mm0` file parses, and its printed form parses back to the same statements: 41
  files, 59,464 statements, including `setmm.mm0`.
- Every `.mmb` file decodes completely, every stream in it re-encodes to its original
  bytes, and `dump` runs to the end: 16 files, 62 MB, including `setmm.mmb`.
- Beyond what was asked: every specification is elaborated, and each of its statements
  is compared with the statement of the proof file. 21 pairs agree, 55,165 statements.
- Three things are not as the sentence above would have them:
  - `examples/verifier.mm1` cannot be compiled by `mm0-rs` ("def Verifier missing
    value"), so that example has a specification (which parses and elaborates) but no
    proof file.
  - `examples/hello_assembler` is an unfinished example. Both files read, but the proof
    file has a theorem where the specification has `def hello`. mm0-c rejects the pair at
    the same statement; the test expects the mismatch.
  - The set.mm translation is read without its index, which `mm0-hs` writes in an old
    layout (see "Open points").

> Unit tests for the parser on hand-written snippets, including malformed input.

- 303 checks on hand-written input, 165 of them malformed inputs that must be rejected
  at a given position with a given message (see "What passes").

### Phase 2 acceptance

> Every valid `.mmb` is accepted by us, including the set.mm translation and every file
> the example sources compile to.

- The proofs of all 15 valid proof files are accepted: the 9 built from the example
  sources and from set.mm (`.tools/corpus`), and the 6 that the MM0 repository ships.
  99,996 statements, 50,595 of them in the set.mm translation. This is a test
  (`tests/Tests/Verify/Corpus.lean`).
- With their specifications: `verify x.mm0 x.mmb` accepts all 9 corpus pairs.
- `hello_assembler.mmb`, the tenth corpus file, is rejected, and should be: one theorem
  is proved with `sorry`, and the file does not match its specification (phase 1).
- The 7 mutants of the MM0 repository that the reader lets through are rejected, each
  with the expected message; the other 14 are rejected by the reader.

> A corpus of mutated `.mmb` files is run through both [...] Any case where we accept
> and `mm0-rs` rejects (or vice versa) is examined before moving on.

`scripts/mutation-campaign.sh`: 31,800 mutants of six valid files (`small`, `conv_all`,
`dummy_thm`, `hol`, `set`, `peano`), each checked by us and by `mm0-rs compile`.

| Verdicts | Mutants |
| -------- | ------- |
| rejected by both | 21,704 |
| accepted by both | 3,049 |
| rejected by us, accepted by `mm0-rs` | 7,047 |
| accepted by us, rejected by `mm0-rs` | 0 |

Every one of the 7,047 is a difference already decided in `MMB-NOTES.md` section 9, and
is recognized as such from our error message:

| Point of section 9 | Mutants |
| ------------------ | ------- |
| 8: `mm0-rs` does not read the proof body of an axiom or definition | 5,896 |
| 11: it ignores the dependency bits of a bound binder | 413 |
| 6: it accepts `Sorry` | 383 |
| 9: it does not compare the sort in the term table with the return type | 276 |
| 20: it does not count statements, nor read table entries that no statement declares | 79 |

In each of these the formal semantics, or mmb.md where they are silent, side with us,
and each has a fixture (`tests/fixtures/disputed`, `tests/fixtures/verify`). Of the 3,049
mutants that both accept, mm0-c rejects 74: all are an `END` byte with data-width bits,
point 21. No mutant made the verifier index out of bounds (`LEAN_ABORT_ON_PANIC=1`).

The same comparison on hand-written files: 50 proof files, one per rule
(`tests/fixtures/verify`). We agree with mm0-c (its build without the `.mm0` parser,
`mm0-c-np`) on 49 of them, all but `many_sorts` (130 sorts, point 22); `mm0-rs` accepts
11 that we reject, by points 8, 10, 11 and 20. mm0-c in turn accepts two of the disputed files that
`mm0-rs` and we reject (points 1 and 7): it is not the reference.

> `mm0-rs` [...] has no command that checks a `.mmb` against a `.mm0`. That step follows
> the formal specification, and is tested on hand-written cases.

- 18 cases on `small.mmb`: the specification as it is, 3 changes that must not matter
  (a def without its value, other names of variables and hypotheses, other names of
  declarations) and 14 that must be caught (modifiers, binders, values, conclusions,
  hypotheses and their order, axiom against theorem, missing and extra statements,
  order).
- 21 real pairs match on all 55,165 statements; the one pair that should not match does
  not.

> Benchmark: set.mm translation verified within 10x of `mm0-c`'s time.

- mm0-c: 0.26 s. Ours: 1.80 s, 6.9 times that (specification 0.89 s, proofs 0.56 s,
  matching 0.35 s). The first version took 3.1 s; what was changed, and why it was slow,
  is in `DESIGN.md`, "The loop, and what the Lean compiler does with it".

### Phase 3 acceptance

> **Replay test**: given an existing set.mm proof as the *sequence of statements used*,
> the engine reconstructs the full proof by unification alone; the emitted `.mmb` passes
> our verifier and `mm0-rs`.

`mm0-whitehead prove replay .tools/corpus/setmm.mmb -o out.mmb`: each proof is reduced
to the tree of the assertions it uses, every expression is forgotten, and the engine
finds the substitutions again.

| | |
| - | - |
| theorems with a proof | 47,611 |
| reconstructed | 47,611 |
| steps | 3,508,182, as in the file |
| tuples of proofs that did not unify; proofs rejected by the verifier | 0; 0 |
| proof bodies | 32.4 MB in the file, 32.7 MB reconstructed |
| time | 77 s on one processor, 8.8 s on 24 (2026-10-12) |

`out.mmb` is accepted by our verifier against `setmm.mm0`, by `mm0-rs`, and by mm0-c.

> **Search test**: a benchmark set of theorems from the set.mm translation (start with
> propositional calculus and predicate calculus sections) proved from scratch under a
> time budget; report the fraction proved and the proof lengths.

`scripts/search-baseline.sh`: every theorem proved from the assertions before it and
nothing else, breadth first, 1 s per theorem, one search per physical core.

| | propositional calculus | predicate calculus |
| - | - | - |
| theorems | 1,520 | 1,262 |
| proved | 816 (53.7%) | 377 (29.9%) |
| proved, 2026-10-12, one search per core (12 at once) | 840 (55.3%) | 422 (33.4%) |
| steps of a proof found: median, largest | 2, 4 | 1, 3 |
| proofs of 0, 1, 2, 3, 4 steps | 2, 26, 509, 270, 9 | 3, 300, 59, 15, 0 |
| shorter than in the file / the same / longer | 15 / 604 / 197 | 233 / 136 / 8 |
| proofs rejected by the verifier | 0 | 0 |

The files with the proofs found are accepted by our verifier against `setmm.mm0` and by
`mm0-rs`. In one second the tree reaches about 500,000 assertion nodes, depth 3 to 4, so
a proof found has at most four steps. Of a sample of 179 theorems from the rest of
set.mm, 3 are proved. With 10 s or 3,000,000 nodes, on a sample of every tenth theorem,
79% of propositional and 49% of predicate calculus are proved (56% and 32% of the same
sample at 1 s), still by proofs of at most four steps. More in `DESIGN.md`, "The search
test".

Both tests were run again on 2026-10-05, with every proof kept (no dedup that is not
proved safe); the tables above are of that run. The search test had 805 and 374 proved
on 2026-10-01, with one proof kept per restricted substitution, and 825 and 383 with
one per whole substitution. The limit is time, so two runs differ; keeping every proof
costs nothing that shows here. The two samples of the paragraph above (the rest of
set.mm, and 10 s) are of the first run.

Definitions (set.mm has none: its `df_*` are axioms there) are unfolded by a step
given by the def and the occurrence in the goal, and inside a variable of the tree by
MM0's conversion rules taken as assertions (`DESIGN.md`, "Unfolding as an inference
step"). On the files with defs compiled from the examples of the MM0 repository, replay
reconstructs every proof that does not share a conversion: 2,650 of 2,700 of `peano`,
3,751 of 3,810 of `peano_hex`, 4,800 of 4,895 of `mm0`, 7,518 of 7,671 of `x86`, 9,909
of 10,124 of `compiler`, 9,919 of 10,134 of `hello_mmc`, 79 of 99 of `hol`, 26 of 26 of
`set`; every output is accepted by our verifier and `mm0-rs`. Searched from scratch at 1 s per
theorem, a sample of every tenth theorem of `peano` has 97 of 270 proved; on the fixture
with definitions, 24 of 26 theorems are proved.

The forward direction (`forward.flow`) was ported after the baseline. On a sample of
every tenth theorem of the two sections, 1 s per theorem:

| | propositional (154) | predicate (127) |
| - | - | - |
| backward, breadth first | 89 | 41 |
| forward alone | 21 | 10 |
| both in turn | 108 | 46 |

All proofs found are accepted by the verifier. Every derivation of a statement is now
a fact of the front (one per application and key, as in the tree); while a statement
was a fact once, forward alone proved 38 of the 281, and both in turn 156 or 157.

### Phase 4: the chains of set.mm (2026-10-13)

`mm0-whitehead prove chains .tools/corpus/setmm.mmb`, chains of 2 to 6 steps, kept
from 2 occurrences; 24 s. 47,611 proofs, 3,508,182 steps.

| chain length | occurrences | distinct, 2 or more times | their occurrences |
| - | - | - | - |
| 2 | 3,460,589 | 187,720 | 3,263,904 (94.3%) |
| 3 | 3,358,854 | 341,988 | 2,689,315 (80.0%) |
| 4 | 3,223,526 | 348,027 | 2,189,045 (67.9%) |
| 5 | 3,071,583 | 322,516 | 1,869,896 (60.8%) |
| 6 | 2,911,366 | 298,376 | 1,635,323 (56.1%) |

Steps on a chain of 2 or more steps that occurs at least: 2 times, 96.5%; 10 times,
86.4%; 100 times, 60.2%; 1,000 times, 23.3%. Of the occurrences of chains of 2, 99,724
reach the root of their proof and 541,717 start at a hypothesis of the theorem; of
chains of 6, 21,104 and 309,550. On `peano` (29,050 steps): 83.6%, 46.3%, 23.4% and
11.2% of the steps at the four thresholds.

An occurrence is counted once per use, so a shared subproof of a large proof counts
every time it is used, and the report also says in how many proofs a chain occurs
(`--mm0 setmm.mm0` gives the names, the translation having no index). The most used
chain of two steps, `renegcli` on `pire` (minus pi is real), occurs 11,088 times in 74
proofs, the Fourier theorems; `syl` on `syl` 9,649 times in 983 proofs, and `adantr`
on `syl` 9,449 times in 1,687. Of six steps: `adantr .0 syl .0 simpld .0 mpbid .1 syl
.1 fourierdlem2`, 2,450 times in 20 proofs.

## Decisions (2026-10-01)

1. The formal semantics are the final judge: `mm0.md` plus the formal specification
   (`examples/mm0.mm0`, `mm0-lean/mm0/*.lean`).
2. `mm0-rs` is the reference implementation, not mm0-c. mm0-c accepts a proof that the
   formal semantics reject (`tests/fixtures/disputed/bound_arg_vars`). mm0-c is kept for
   the speed comparison.
3. For `.mm0` files the reference is `mm0.md` plus the formal specification.
4. The reader supports `import`.
5. The verifier compares expressions by node identity; no hash-consing there.
6. `free` sorts: as both implementations do (no dummy of a `free` sort; every free
   variable of a def's value among the dependencies of its return type).

`CLAUDE.md` states this order of authority; `MMB-NOTES.md` section 9 applies it to each
point on which the sources differ, and `DESIGN.md` does the same for the `.mm0` grammar.

## Decisions (2026-10-12)

1. The three places of the Russell source that look unintended (`ruCheckDisjs` in
   `ruAddProof`, the variable set of `ruMakeFresherSubst`, the argument order of
   `ruSuperRule` in `unify_var`; `DESIGN.md`, changes 2–4): the port keeps what it does
   at each, which is what MM0 needs.
2. The limits of the forward front: completeness is needed, so no variant is thrown
   away; a bound on the growth of the tree is acceptable when it is configurable, as
   the backward tree's are, because it can always be raised. The size of the front was
   configurable (`--max-facts`, 512); the number of facts a new subgoal is joined with
   (`fwd_cap`, 4) was a constant and is `--join-cap N|all`. Built.
3. The tests are in two layers: `lake test`, fast, and `lake exe thorough`, which runs
   the prover over every proof file within a time of about 30 minutes, with a stride
   (every 10th theorem) where a full run would be too long. Built (below).

## Decisions (2026-10-05)

1. A disjoint-variable condition on a fresh name is dropped once the name does not
   occur in the statement of the parent `RuProverExp` under the proof's substitution.
   This is what the code did.
2. All variants of a proof are needed, and a proof is dropped only where it is proved
   that this is safe. The two places where the Russell source keeps one proof of
   several have no such proof (`ruProofSubKey` in `ruAddProof`; the set `seen` and "one
   proof per matched fact" in `ruApplyForward`), so the port kept every proof of an
   assertion node, and every derivation of a statement as a fact of the forward front.
   Refined on 2026-10-11: proofs with identical restrictions on the free variables may
   be merged, so one proof is kept per key — the substitution restricted to the
   parent's variables with the open conditions (`proofKey`; `DESIGN.md`, change 5).
3. A variable of a goal is a free variable or a metavariable, by a mark. How the mark is
   written is a stub, MM0 having no syntax for it: `prove search --meta`.
4. `>` in the type of a `def` (`def all: type > term;`, five statements in
   `examples/hol.mm0`; neither `mm0.md` nor the formal specification has it): as `mm0-rs`
   does, which accepts it. So did the parser already.
5. Unfolding a definition is a proof step of its own, not a part of unification; and an
   expansion is granular: one node at a time, all variants of one step (2026-10-06). An
   unfolding step is a def and an occurrence in the goal; MM0's conversion proof is
   written at emission. Built.

## What passes

`MM0_REPO=/path/to/mm0 lake test`, with the tools of `scripts/build-oracles.sh` and the
corpus of `scripts/build-corpus.sh` built — 928 checks, 0 failures, in 18 seconds:

- `.mm0`, hand-written: 123 lexer and parser checks (69 rejections); 11 checks of
  `import` resolution (5 rejections); 97 checks of formulas, notations and declarations
  (53 rejections).
- `.mmb`, hand-written: 72 reader checks (38 rejections). One file is compared field by
  field with its annotated listing in `MMB-NOTES.md`; a second, with an index, is decoded
  and its dump compared with a checked-in text.
- `.mm0` corpus: 41 specifications parse and round-trip through the printer. 25 files of
  `tests/mm0_mmu/fail`: 24 rejected, one accepted because it is grammatical. The 9
  example specifications with `import` join to the same statements as with `mm0-rs join`.
- `.mmb` corpus: 16 proof files decode, round-trip and dump. Of the 21 mutated files of
  the MM0 repository, the reader rejects the 14 it should and decodes the 7 that are
  wrong only for a verifier.
- Verifier, hand-written: `small.mmb` and the 7 disputed files; 50 files with one rule
  each, with our verdict and those of `mm0-rs` and mm0-c (`mm0-c-np`); 18 specification
  cases.
- Verifier, corpus: 15 valid proof files accepted, 1 invalid file and 7 mutants rejected.
- Prover, hand-written and random: expressions and substitutions; unification and the
  index, also compared with a reference unifier on 27,000 random inputs; the product
  unifier against trying every tuple on 3,000 random products, and the tuples of a
  product one at a time; the engine on the logic
  fixture (database, replay of its 16 proofs, breadth-first search, the forward
  direction and both in turn, conditions on bound variables, one proof per key kept in
  the tree and in the forward front and none made twice, variables marked as
  metavariables and the values found for them).
- Prover, the chain miner: its counts by length, the most frequent chain and the
  coverage on the logic fixture.
- Prover, definitions: the values of the defs of the fixture `defs.mmb` (a copy of
  `examples/set.mm1`), the rule made for an unfolding, the expansion of a goal by its
  unfoldings and foldings, an unfolding inside a variable by the conversion rules and
  its emission as `Conv`, 24 of its 26 theorems proved from scratch (the test asks for
  20) and all 26 replayed, the files verified; the full replay of both fixtures with
  0, 4 and all other variants, and in rounds.
- Prover, corpus: the theorems of set.mm numbered below 6,000 (5,899 proofs) replayed,
  and `peano.mmb` — 2,650 of its 2,700 proofs, the 50 that share a conversion left
  out — the resulting files verified.
- Pairs: 22 specification/proof pairs (8 fixtures of this repository, 4 pairs of the MM0
  repository, 10 of the built corpus). 21 agree on every statement, 55,165 in all; one is
  the expected mismatch.

Without `MM0_REPO` the `.mm0` corpus group is skipped; without the built corpus the
other corpus groups and the pairs are reduced to what the repository holds, and the
prover's corpus group is skipped; without `.tools/bin` the verdicts of `mm0-rs` and
mm0-c are not compared. Each is reported.

That is the fast layer. `MM0_REPO=/path/to/mm0 lake exe thorough` is the thorough one
(`DESIGN.md`, "Two layers"): the prover over every proof file there is, within 30
minutes, every 10th theorem where a sample is taken, one theorem per processor (24)
and one search per physical core (12). Run on 2026-10-12 — 153 checks, 0 failures,
1 skip (`hello_assembler`, for its `sorry`), in 29 minutes:

- Replay of every proof of 15 files in full: the 9 of the corpus and the 6 that the
  MM0 repository ships. Every proof without a shared conversion is reconstructed, step
  for step; set.mm's 47,611 in 12 s. Each file with the new bodies is accepted by our
  verifier, matches its specification where there is one, and is accepted by `mm0-rs`.
- Search samples, 1 s per theorem: of propositional and predicate calculus of set.mm,
  backward 138 of 281 and in both directions 167 of 281; of `peano`, 90 of 270. No
  proof found was rejected, and the files are checked as above.
- Replay over the full expansion, in rounds: the 11 files with fewer than 6,000
  theorems in full — none stopped at a limit but 12 of the 4,895 of `mm0` — and
  `x86`, `compiler`, `hello_mmc` and set.mm every 10th theorem: 4 of 765, 4 of 1,011,
  4 of 1,012, and 100 of 4,778 of set.mm in the 25 minutes it had (5 rounds, up to
  256 s per theorem), 29 of set.mm's proofs found not the known one. No tuple of a
  known proof failed to unify, and no proof was rejected. The allowance is 5%: the
  whole of set.mm, with two hours, has 2.9% at a limit.

Also checked by hand: `mm0-rs compile` accepts the output of `mm0-whitehead join` for
`x86`, `mm0`, `peano_hex`, `verifier`, `compiler` and `hello_mmc`; and a test signature
with every kind of notation gives the same trees through `mm0-rs` as through our
elaborator.

Timings (`mm0-whitehead bench`, one run each; the dump row by the shell's `time`):

| Input | Size | Time |
| ----- | ---- | ---- |
| `setmm.mm0`, parse | 20 MB, 50,596 statements | 0.20 s |
| `setmm.mm0`, load and elaborate | 49,156 axioms and theorems | 0.89 s |
| `setmm.mmb`, open | 39 MB, 50,595 statements | 0.008 s |
| `setmm.mmb`, decode every stream | 21.2 million commands | 0.35 s |
| `setmm.mmb`, dump to a pipe | 15.6 million lines, 390 MB | 3.5 s |

`mm0-whitehead verify setmm.mm0 setmm.mmb` takes 1.80 s; mm0-c takes 0.26 s, so the
phase 2 budget of ten times that is 2.6 s.

## Tools and corpus

`scripts/build-oracles.sh` and `scripts/build-corpus.sh` (see `DESIGN.md`). Verdicts of
the two implementations on the corpus, as printed by `build-corpus.sh` (exit codes):

| Pair | `.mmb` size | `mm0-rs` | mm0-c | Note |
| ---- | ----------- | -------- | ----- | ---- |
| `hol` | 54 KB | 0 | 0 | |
| `set` | 11 KB | 0 | 0 | the hand-written `examples/set.mm1`, not set.mm |
| `peano` | 0.96 MB | 0 | 0 | |
| `peano_hex` | 1.2 MB | 0 | 0 | |
| `mm0` | 1.8 MB | 0 | 0 | |
| `x86` | 3.3 MB | 0 | 0 | |
| `compiler` | 4.5 MB | 0 | 0 | |
| `hello_mmc` | 4.5 MB | 0 | 0 | |
| `hello_assembler` | 4.5 MB | 0 | 255 | one theorem is proved with `sorry` |
| `setmm` | 39 MB | 0 | 0 | the local set.mm: 49,156 axioms and theorems |

`examples/verifier.mm1` has a specification but `mm0-rs` cannot export it ("def Verifier
missing value"), so there is no pair for it.

Installed for this, outside the repository: Rust 1.98.1 as an additional `rustup`
toolchain (the default toolchain is unchanged), and GHC 8.6.5 through `stack`.

## Open points

1. **Checking a `.mmb` against its `.mm0`** has no counterpart in `mm0-rs`. That step
   follows the formal specification and is tested on hand-written cases and on the
   corpus pairs.
2. **The index of the set.mm translation** is in an old layout that `mm0-rs` rejects; the
   corpus script removes it. Our reader reads the current layout only, so `setmm.mmb`
   dumps with generated names (`T5198`); the real names are in `setmm.mm0`.
3. **Phase 3** (`DESIGN.md`, "The prover", "Questions"). Answered on 2026-10-01: forward
   expansion is ported; unfolding is to be an inference step that looks like an
   assertion to the layer above. Answered on 2026-10-05: the decisions above, all
   built (decision 2 as refined on 2026-10-11). Answered on 2026-10-12: the three
   places of the source stay as the port has them, and the forward limits are
   configurable. No question of phase 3 is open; phase 4 has six, in `DESIGN.md`,
   "Phase 4", "Questions (2026-10-13)".

## Next steps

0. The full replay of the whole of set.mm (2026-10-12): 46,254 of 47,611 in 1 h 57 min,
   1,357 at a limit, none rejected (`DESIGN.md`), with one budget for every theorem.
   To run again in rounds (`--total`), with and without other variants: on the first
   6,000 with two other variants a few theorems take most of the time and stop at the
   tuple limit — the proofs of the alternatives multiply through the joins
   (`DESIGN.md`, "Concurrency, memory, speed").
1. Shared conversions (`ConvCut`, `ConvSave`) in the replay reader: 20 of the 99 proofs
   of `hol` use them.
2. For tasks with metavariables: a way to write the marking, and a check of the proof
   found (it proves an instance of the theorem, which no file states).
3. The cost of joins in a search in both directions (see the forward report above):
   which joins a strategy admits is the lever that Russell's tactic layer has. The
   clock and the memory are now looked at before each forward application and between
   joins, and a join sees the deadline; the case of a front of 2,048 facts, where a
   search once ran for minutes past its limit, has not been measured again.
4. Phase 4: the design waits on the answers to its questions (`DESIGN.md`, "Phase 4").
