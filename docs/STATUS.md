# Status

Last updated: 2026-10-01.

## Phase

**Phase 1 — readers**: done; the acceptance tests pass (report below).
**Phase 2 — independent verifier**: in progress.

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

## What passes

`MM0_REPO=/path/to/mm0 lake test`, with the corpus of `scripts/build-corpus.sh` built —
437 checks, 0 failures, in 8 seconds:

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
| `setmm.mm0`, load and elaborate | 49,156 axioms and theorems | 0.94 s |
| `setmm.mmb`, open | 39 MB, 50,595 statements | 0.008 s |
| `setmm.mmb`, decode every stream | 21.2 million commands | 0.35 s |
| `setmm.mmb`, dump to a pipe | 15.6 million lines, 390 MB | 3.5 s |

For scale, mm0-c verifies the set.mm translation in 0.26 s, so the phase 2 budget of ten
times that is 2.6 s.

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

1. **Arrows in `def`** (`def all: type > term;`, five statements in `examples/hol.mm0`)
   are accepted although neither `mm0.md` nor the formal specification has them
   (`DESIGN.md`). Asked on 2026-10-01; details given, no decision yet.
2. **Checking a `.mmb` against its `.mm0`** has no counterpart in `mm0-rs`. That step
   follows the formal specification and is tested on hand-written cases and on the
   corpus pairs.
3. **The index of the set.mm translation** is in an old layout that `mm0-rs` rejects; the
   corpus script removes it. Our reader reads the current layout only, so `setmm.mmb`
   dumps with generated names (`T5198`); the real names are in `setmm.mm0`.

## Next steps

Phase 2, once phase 1 is confirmed and open points 1 and 2 are answered:

1. The proof stack machine of `MMB-NOTES.md` section 6 on the bytes of the file, with the
   fixtures of `tests/fixtures/disputed` as its first tests.
2. The well-formedness conditions on the environment, and the match between the
   specification and the proof file (the pair test, promoted to a check).
3. `tests/mutate`, and the differential run against `mm0-rs`.
