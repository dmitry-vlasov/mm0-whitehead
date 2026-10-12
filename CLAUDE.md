# mm0-whitehead — project brief for Claude Code

## What this project is

`mm0-whitehead` is a Lean 4 implementation of tooling for **Metamath Zero (MM0)**:

1. a reader for the `.mm0` specification format and the `.mmb` binary proof format;
2. an **independent verifier** for MM0, written in Lean, implementing the formal
   semantics of MM0 and cross-checked against the reference implementation `mm0-rs`;
3. an **automated prover** for MM0, based on the proof-search engine of the author's
   earlier system *Russell* (a Metamath-based prover), emitting `.mmb` proofs that
   our verifier and `mm0-rs` accept;
4. later: proof-pattern mining ("linear subproofs") and a learned ranking layer on top of
   the prover.

The phases are strictly ordered. **Do not start phase N+1 before phase N has passed its
acceptance tests** (defined below). The name: Whitehead was Russell's co-author on
*Principia Mathematica*; this is the MM0 companion of the Russell prover.

Reference material (read before writing code):
- MM0 repository: https://github.com/digama0/mm0 — the format specifications
  (`mm0.md` for `.mm0`, `mm0-c/mmb.md` for the `.mmb` binary format), the formal
  specification, the implementations, plus the `examples/` directory.
- The paper: M. Carneiro, *Metamath Zero: The Cartesian Theorem Prover* (CADE 2020).

Who is right when sources disagree, in this order:

1. **The formal semantics are the final judge**: `mm0.md` together with the formal
   specification `examples/mm0.mm0` (mirrored in Lean in `mm0-lean/mm0/mm0.lean`, with
   the MMB stack machine in `mm0-lean/mm0/mm0b.lean`). They define what a valid
   specification is and what "verify" means. For `.mm0` files the reference is
   `mm0.md` plus the formal specification, not any implementation's parser.
2. **`mm0-rs` is the reference implementation**: the `.mmb` reader
   (`mm0-rs/components/mm0b_parser`), the kernel (`mm0-rs/src/elab/verify.rs`), the
   `.mm0`/`.mm1` parser (`mm0-rs/components/mm1_parser`) and `import`
   (`mm0-rs/src/joiner.rs`). Where the formal semantics are silent — file layout,
   framing, the index — follow `mm0-rs`.
3. `mm0-c/mmb.md` is the written description of the `.mmb` format.
4. **`mm0-c` is not a reference.** It accepts proofs that the formal semantics reject
   (`docs/MMB-NOTES.md`). It may be run as an additional comparison, and it is the
   speed yardstick, but a disagreement with it is not by itself a bug.

`import "file";` in `.mm0` files is an `mm0-rs` extension that is not in `mm0.md`; the
example files use it and our reader must support it.

Local checkouts:
- MM0: a checkout of the MM0 repository, named by `MM0_REPO` (`mm0.md`, `mm0-c/mmb.md`, `examples/`, `mm0-rs/`,
  `mm0-lean/`, `mm0-c/`, `tests/`).
- Russell: a checkout of `russell-flow` beside this repository (see the next section).

When the formal semantics and `mm0-rs` disagree, follow the formal semantics and record
the case in `docs/MMB-NOTES.md`. When the sources above do not settle a question, or
when something is unclear, **stop and ask** rather than guessing.

## Russell — the reference implementation of the prover

Phase 3 ports an existing, working engine; it does not design a new one.

- **Russell is written in Flow9**, a simple yet powerful functional language of the ML
  family: immutable records, algebraic types dispatched with `switch`, first-class
  functions, explicit state threading, path-based imports (`import ru/src;` →
  `src/ru/src.flow`). Translating Flow9 to Lean is therefore mostly direct: structs
  become `structure`s, unions become `inductive`s, `switch` becomes `match`. Read
  `CLAUDE.md` of the Russell checkout for the Flow9 notes and the layout of that
  repository.
- **The Russell source code is the final judge.** For anything in the prover — the
  proof variant tree, expansion, unification, substitution composition, indexing, proof
  extraction — first look at how Russell implements it, then translate that to the Lean
  MM0 environment. Do not re-derive an algorithm from its description when the source
  is there to read; a discrepancy between this brief (or a doc) and the Russell source
  is resolved in favour of the source, and is worth raising. Cite the Flow9 file and
  function being translated in the commit message or in `DESIGN.md`.
- Where to look:
  - engine: `src/ru/prover/core/` (`tree.flow`, `expand.flow`, `prove.flow`,
    `env.flow`, `proofs.flow`, …);
  - unification and indexing: `src/ru/unify/`, `src/ru/subst.flow`, `src/ru/index.flow`;
  - strategies: `src/ru/prover/tactics/` (the layer above the engine);
  - linear chains and learning (phase 4): `src/ru/prover/commands/find_linear_chains.flow`,
    `src/ru/prover/ml/`;
  - docs: `docs/proof-search-algorithm.md`, `docs/unification-algorithms.md`.
- **Completeness has a proof**: `docs/proof_search_algo.pdf` (D. Vlasov, *Proof Search
  Algorithm in Pure Logical Framework*) proves correctness, generality and completeness
  of Russell's algorithm. The Lean port must stay within the algorithm that proof covers;
  where MM0 forces a change (bound variables and dependency constraints, definitions and
  `unfold`), write down how the change relates to the proof and ask.

## Technology and constraints

- Lean 4, application code. **No Mathlib dependency.** Core `Std` (`HashMap`, `HashSet`,
  `ByteArray`, `Array`) is the standard library; add `Batteries` only if a concrete need
  arises, and say why.
- `lakefile.toml` has `autoImplicit = false`. Keep it. Every variable is declared.
- `lean-toolchain` is pinned; do not bump it without asking.
- Performance matters from phase 2 on: `mm0-c` checks the set.mm translation in well
  under a second; our target is within an order of magnitude.
  Lean performance idioms to respect:
  - keep `Array`/`ByteArray` updates in place by never holding a second reference to
    the array being mutated (uniqueness); prefer `modify`/`set!` in loops over
    functional rebuilds;
  - avoid `List` in hot paths; use `Array` and indices;
  - `partial def` and `unsafe` are acceptable in the engine and I/O code — this is a
    program, not a proof library; do not spend effort on termination proofs for
    interpreters and search loops;
  - measure before optimizing: add a `bench` executable target early and report timings
    in PR descriptions.
- Code organization: one concept per module under `Whitehead/` (e.g. `Whitehead/Mm0/Syntax.lean`,
  `Whitehead/Mmb/Reader.lean`, `Whitehead/Verify/*.lean`, `Whitehead/Prove/*.lean`),
  a thin `Main.lean` CLI with subcommands (`verify`, `prove`, `bench`, `dump`).
- Tests live under `tests/`, run by `lake test` (or a `test` exe target). Every phase
  adds tests before features.
- Keep `docs/DESIGN.md` up to date: data structures, the proof-tree model, decisions
  taken and why. Keep `docs/MMB-NOTES.md` as our own description of the `.mmb` format as
  understood from the spec and from reading `mm0-rs` — it must be enough for someone to
  re-implement the reader from it.

## Phase 1 — readers

Deliverables:
- `.mm0` parser (parser combinators from core `Std.Internal.Parsec` are fine; no need for
  a parser generator): sorts, term declarations with binder/dependency information,
  axioms, theorems (statements only), `def`s, notation declarations needed to parse the
  example files, and `import`. Produce an AST with source positions and good error
  messages.
- `.mmb` reader: full decoding of the binary format into in-memory structures — the
  statement table, the term/theorem/def tables, and the **proof instruction streams**
  (the `.mmb` proof format is a stack machine; decode instructions faithfully, including
  save/reuse of subproofs and `unfold`).
- `dump` subcommand that pretty-prints a decoded `.mmb` (statements and proofs) in a
  readable text form, for debugging and for diffing against `mm0-rs` output where
  available.

Acceptance:
- All example `.mm0`/`.mmb` pairs in the MM0 repository, and the set.mm translation,
  parse/decode without error and round-trip through `dump` consistently.
- Unit tests for the parser on hand-written snippets, including malformed input.

## Phase 2 — independent verifier

Deliverables:
- `verify <file.mm0> <file.mmb>` that checks a `.mmb` proof file against its `.mm0`
  specification, implementing MM0's checks: sort/term/binder well-formedness, bound
  variable and dependency conditions, definition well-formedness and conservativity
  conditions, `unfold` side conditions, and the proof stack machine.
- A verifier that is **structurally close to the MM0 semantics formalization**, so that
  it can be verified against it later. Prefer clarity over cleverness in the checking
  logic; put performance work in the data representation (arrays, in-place stacks), not
  in the logic.
- Expressions are compared by **node identity**, as the format, `mm0b.lean` and `mm0-rs`
  do: a node is its allocation index in a per-statement store. No hash-consing in the
  verifier (it would accept files the format rejects); hash-consing is for the prover.

Acceptance (differential testing against `mm0-rs`, with the formal semantics as the
judge of any disagreement):
- Every valid `.mmb` is accepted by us, including the set.mm translation and every file
  the example sources compile to.
- A corpus of **mutated** `.mmb` files (bit flips, swapped instructions, altered
  statements, broken dependency declarations) is run through both; add a `tests/mutate`
  tool that generates them. Any case where we accept and `mm0-rs` rejects (or vice
  versa) is examined before moving on: it is a bug in our verifier unless the formal
  semantics side with us, in which case it is recorded in `docs/MMB-NOTES.md` with a
  fixture.
- `mm0-rs` reads and checks a `.mmb` on its own (`mm0-rs compile file.mmb`); it has no
  command that checks a `.mmb` against a `.mm0`. That step follows the formal
  specification, and is tested on hand-written cases.
- Benchmark: set.mm translation verified within 10x of `mm0-c`'s time.

## Phase 3 — prover (the Russell engine, ported)

The engine model, to be implemented as specified here and **as implemented in Russell**
(see "Russell — the reference implementation of the prover" above: the Flow9 source is
the final judge; see `docs/DESIGN.md` for the evolving details):

- **Proof variant tree**: a set of rule-labelled DAGs connecting premises (hypotheses,
  already-proved statements) to a goal. Nodes are statements possibly containing
  **metavariables**; edges are labelled by the MM0 theorem/axiom/definition used.
  The tree can be expanded in both directions: *backward* (which rules could conclude
  this goal) and *forward* (what follows from this premise).
- **Expansion is unification-driven**: to expand a node against the database, compute
  for every applicable statement the **most general unifier** (first-order syntactic
  unification over MM0 expressions, with MM0's bound-variable/dependency constraints
  carried as constraints on the substitution and discharged consistently). Never guess
  instantiations: metavariables are instantiated only by unification. Metavariables are
  allowed in the initial goal and premises; the prover must then *find* substitutions
  that make the goal provable (Prolog-style answer substitutions).
- **Soundness by construction**: every closed path in the tree corresponds to a valid
  MM0 proof; emit it as `.mmb` and check it with our verifier and with `mm0-rs`.
- **Completeness**: with a fair expansion strategy (iterative deepening or equivalent),
  any existing proof is found. The engine must not lose this property; ranking and
  heuristics live in a separate layer that only chooses *which* existing variants to
  expand next.
- **Indexing**: "all statements unifying with this expression" must be fast at set.mm
  scale — implement a discrimination tree (or substitution tree) over MM0 expressions.
- **Layering**: (1) engine = tree + unifier + index + `.mmb` emission; (2) oracles for
  theory reasoning (to be designed later; they must produce `.mmb` certificates, never
  tree expansions); (3) strategies/policies choosing expansions. Keep the layers in
  separate modules with explicit interfaces.

Acceptance:
- **Replay test**: given an existing set.mm proof as the *sequence of statements used*,
  the engine reconstructs the full proof by unification alone; the emitted `.mmb` passes
  our verifier and `mm0-rs`. This tests the unifier and emission on real data.
- **Search test**: a benchmark set of theorems from the set.mm translation (start with
  propositional calculus and predicate calculus sections) proved from scratch under a
  time budget; report the fraction proved and the proof lengths. This is the baseline
  for all later ranking work.

## Phase 4 — pattern mining and ranking (research layer)

- Mine **linear subproofs** (chains of single-rule steps from a premise to a goal)
  across the set.mm translation; anti-unify occurrences into generalized schemas with
  frequencies; expose them to the prover as macro-actions (derived rules with one
  unifier each). Measure coverage and out-of-sample replay success.
- A clean environment API (state = tree frontier, action = (node, variant)) for learned
  policies; dataset export for training premise-ranking models.
Design only after phase 3's search baseline exists.

## How to work

- Start by reading the MM0 spec and `mm0-rs`, then write `docs/MMB-NOTES.md`; show it
  to me before writing the reader.
- Work in small, reviewable steps: one module or one feature per PR-sized change, with
  tests. Explain Lean-specific choices (uniqueness/in-place updates, `partial`, data
  representation) in commit messages or `DESIGN.md`.
- Do not introduce abstractions speculatively; three concrete uses before a
  generalization.
- When unsure about MM0 semantics, write the question down and ask; do not pick an
  interpretation silently.
- Keep a `docs/STATUS.md` with the current phase, what passes, what's open.
