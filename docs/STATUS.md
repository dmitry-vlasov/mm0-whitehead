# Status

Last updated: 2026-10-05.

## Phase

**Phase 1 — readers**: done; the acceptance tests pass (report below).
**Phase 2 — independent verifier**: done; the acceptance tests pass (report below).
**Phase 3 — prover**: the engine is ported, in both directions; both acceptance tests
are run (report below). Open: definitions, and the questions of `DESIGN.md`.

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

The same comparison on hand-written files: 48 proof files, one per rule
(`tests/fixtures/verify`). We agree with mm0-c on all 48; `mm0-rs` accepts 11 that we
reject, by points 8, 10, 11 and 20. mm0-c in turn accepts two of the disputed files that
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
| time | 70 to 90 s |

`out.mmb` is accepted by our verifier against `setmm.mm0`, by `mm0-rs`, and by mm0-c.

> **Search test**: a benchmark set of theorems from the set.mm translation (start with
> propositional calculus and predicate calculus sections) proved from scratch under a
> time budget; report the fraction proved and the proof lengths.

`scripts/search-baseline.sh`: every theorem proved from the assertions before it and
nothing else, breadth first, 1 s per theorem.

| | propositional calculus | predicate calculus |
| - | - | - |
| theorems | 1,520 | 1,262 |
| proved | 825 (54.3%) | 383 (30.3%) |
| steps of a proof found: median, largest | 2, 4 | 1, 3 |
| proofs of 0, 1, 2, 3, 4 steps | 2, 26, 512, 276, 9 | 3, 300, 64, 16, 0 |
| shorter than in the file / the same / longer | 15 / 610 / 200 | 233 / 141 / 9 |
| proofs rejected by the verifier | 0 | 0 |

The files with the proofs found are accepted by our verifier against `setmm.mm0` and by
`mm0-rs`. In one second the tree reaches about 500,000 assertion nodes, depth 3 to 4, so
a proof found has at most four steps. Of a sample of 179 theorems from the rest of
set.mm, 3 are proved. With 10 s or 3,000,000 nodes, on a sample of every tenth theorem,
79% of propositional and 49% of predicate calculus are proved (56% and 32% of the same
sample at 1 s), still by proofs of at most four steps. More in `DESIGN.md`, "The search
test".

Both tests were run again on 2026-10-05, after the change in which proofs are kept (one
per whole substitution, as in Russell); the tables above are of that run. The run of
2026-10-01 had 805 and 374 proved. The limit is time, so two runs differ, and whether
this difference comes from the change is not known; keeping all variants costs nothing
that shows here. The two samples of the paragraph above (the rest of set.mm, and 10 s)
are of the earlier run.

What is not done of the engine model of the brief: definitions are not unfolded
(set.mm has none; a proposal is in `DESIGN.md`).

The forward direction (`forward.flow`) was ported after the baseline. On a sample of
every tenth theorem of the two sections, 1 s per theorem:

| | propositional (154) | predicate (127) |
| - | - | - |
| backward, breadth first | 91 | 41 |
| forward alone | 28 | 10 |
| both in turn | 108 | 48 |

All proofs found are accepted by the verifier.

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

## Decisions (2026-10-05)

1. A disjoint-variable condition on a fresh name is dropped once the name does not
   occur in the statement of the parent `RuProverExp` under the proof's substitution.
   This is what the code did.
2. All variants of a proof are needed: keeping one proof per restricted substitution
   breaks completeness. `addProof` keeps one per whole substitution, as `ruAddProof`.
3. A variable of a goal is a free variable or a metavariable, by a mark. How the mark is
   written is a stub, MM0 having no syntax for it: `prove search --meta`.
4. `>` in the type of a `def` (`def all: type > term;`, five statements in
   `examples/hol.mm0`; neither `mm0.md` nor the formal specification has it): as `mm0-rs`
   does, which accepts it. So did the parser already.

## What passes

`MM0_REPO=/path/to/mm0 lake test`, with the corpus of `scripts/build-corpus.sh` built —
828 checks, 0 failures, in 13 seconds:

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
- Verifier, hand-written: `small.mmb` and the 7 disputed files; 48 files with one rule
  each, with our verdict and those of `mm0-rs` and mm0-c; 18 specification cases.
- Verifier, corpus: 15 valid proof files accepted, 1 invalid file and 7 mutants rejected.
- Prover, hand-written and random: expressions and substitutions; unification and the
  index, also compared with a reference unifier on 27,000 random inputs; the engine on
  the logic fixture (database, replay of its 16 proofs, breadth-first search, the
  forward direction, conditions on bound variables, two proofs that differ only below a
  node both kept, variables marked as metavariables and the values found for them).
- Prover, corpus: the first 6,000 statements of set.mm replayed, the resulting file
  verified.
- Pairs: 22 specification/proof pairs (8 fixtures of this repository, 4 pairs of the MM0
  repository, 10 of the built corpus). 21 agree on every statement, 55,165 in all; one is
  the expected mismatch.

Without `MM0_REPO` and the corpus the last three groups are skipped or reduced, and that
is reported.

Also checked by hand: `mm0-rs compile` accepts the output of `mm0-whitehead join` for
`x86`, `mm0`, `peano_hex`, `verifier`, `compiler` and `hello_mmc`; and a test signature
with every kind of notation gives the same trees through `mm0-rs` as through our
elaborator.

Timings (`mm0-whitehead bench`, one run each):

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
   built. Still open:
   3. what to do about an unfolding inside a variable of the goal: an example and three
      ways to go on are in `DESIGN.md`;
   6. three places in the Russell source that look unintended (for the author to
      investigate): `ruCheckDisjs` in `ruAddProof`, the variable set in
      `ruMakeFresherSubst`, the argument order of `ruSuperRule` in `unify_var`;
   8. whether "all variants" also means the two places where the Russell source itself
      keeps one proof of several: `ruProofSubKey` in `ruAddProof`, and one proof per
      fact in `ruApplyForward`.

## Next steps

1. The answers to the questions above.
2. Unfolding as an inference step, once the proposal in `DESIGN.md` is agreed.
3. For tasks with metavariables: a way to write the marking, and a check of the proof
   found (it proves an instance of the theorem, which no file states).
4. The cost of joins in a search in both directions (see the forward report above):
   which joins a strategy admits is the lever that Russell's tactic layer has.
5. Phase 4 is designed only after the search baseline is accepted.
