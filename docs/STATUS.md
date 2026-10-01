# Status

Last updated: 2026-10-01.

## Phase

**Phase 1 — readers**, in progress.

| Deliverable | State |
| ----------- | ----- |
| `docs/MMB-NOTES.md` | reviewed; reworked on the formal semantics and `mm0-rs` |
| `.mm0` primary parser (statements, binders, source positions, error messages) | done, tested |
| `.mm0` `import` | done, tested against `mm0-rs join` |
| `.mm0` secondary parser (math strings, notations, coercions) | not started |
| `.mmb` reader | done, tested on the whole corpus |
| `dump` for `.mm0`, `join` | done |
| `dump` for `.mmb` | done |
| acceptance corpus (example pairs, set.mm translation) | built, by script |
| Phase 1 acceptance | not reached |

## Decisions (2026-10-01)

1. The formal semantics are the final judge: `mm0.md` plus the formal specification
   (`examples/mm0.mm0`, `mm0-lean/mm0/*.lean`).
2. `mm0-rs` is the reference implementation, not mm0-c. mm0-c accepts a proof that the
   formal semantics reject (`tests/fixtures/disputed/bound_arg_vars`).
3. For `.mm0` files the reference is `mm0.md` plus the formal specification.
4. The reader supports `import`.

`CLAUDE.md` states this order of authority; `MMB-NOTES.md` section 9 applies it to each
point on which the sources differ, and `DESIGN.md` does the same for the `.mm0` grammar.

## What passes

`MM0_REPO=/path/to/mm0 lake test`, with the corpus of `scripts/build-corpus.sh` built —
318 checks, 0 failures, in 6 seconds:

- `.mm0`, hand-written: 123 lexer and parser checks, 69 of them malformed inputs with the
  error position and message checked; 11 checks of `import` resolution.
- `.mmb`, hand-written: 72 reader checks. One file is compared field by field with its
  annotated listing in `MMB-NOTES.md`; 38 corruptions of the two fixture files (one or a
  few bytes each, or a truncation) are each rejected at the expected offset with the
  expected message; a second file with an index is decoded and its dump compared with a
  checked-in text.
- `.mm0` corpus: 41 specifications parse and round-trip through the printer (21 MB,
  59,464 statements; this includes `setmm.mm0`). 25 files of `tests/mm0_mmu/fail`: 24
  rejected, one accepted because it is grammatical. The 9 example specifications with
  `import` join to the same statements as with `mm0-rs join`.
- `.mmb` corpus: 16 proof files decode completely (62 MB; the examples, the set.mm
  translation, the files of the MM0 repository). All 109,368 unify streams and
  21,695,564 proof commands, decoded and encoded again, give the original bytes, and
  every file dumps. Of the 21 mutated files of the MM0 repository, the reader rejects
  the 14 it should and decodes the 7 that are wrong only for a verifier.

Without `MM0_REPO` and the corpus those two groups are skipped and reported (206 checks).

Also checked by hand: `mm0-rs compile` accepts the output of `mm0-whitehead join` for
`x86`, `mm0`, `peano_hex`, `verifier`, `compiler` and `hello_mmc`.

Timings (`mm0-whitehead bench`, one run each):

| Input | Size | Time |
| ----- | ---- | ---- |
| `setmm.mm0`, parse | 20 MB, 50,596 statements | 0.20 s |
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

Questions that the sources do not settle, or where what was done goes beyond them. None
blocks the `.mmb` reader.

1. **`free` sorts** (`MMB-NOTES.md` section 9, point 5). `mm0.md` and `mm0.mm0` give three
   different readings; both implementations do the strictest thing. Proposal: do the
   same. To confirm before phase 2.
2. **Identity, not hash-consing, in the verifier** (point 18). The brief puts
   hash-consing among the performance techniques for phase 2. The format, `mm0b.lean`
   and both implementations compare expressions by node identity, and a hash-consing
   verifier would accept files they reject. Proposal: identity in the verifier,
   hash-consing in the prover. To confirm before phase 2.
3. **Arrows in `def`** are accepted because `examples/hol.mm0` needs them, although
   neither `mm0.md` nor the formal specification has them (`DESIGN.md`).
4. **Checking a `.mmb` against its `.mm0`** has no counterpart in `mm0-rs`. That step
   will follow the formal specification; mm0-c is the only other implementation of it
   and can serve as a comparison there. mm0-c is also kept as the speed yardstick.
5. **The index of the set.mm translation** is in an old layout that `mm0-rs` rejects; the
   corpus script removes it. Our reader reads the current layout only, so `setmm.mmb`
   dumps with generated names (`T5198`); the real names are in `setmm.mm0`.

## Next steps

1. The secondary parser for math strings (delimiters, `prefix`/`infix`/`notation`,
   coercions) and the elaboration of a specification into sorts, terms and statements
   with expression trees. Its strongest test is available already: for every pair of the
   corpus, each public statement of the `.mm0` file must come out as the same tree as the
   unify stream of its `.mmb` counterpart.
2. The phase 1 acceptance run over the corpus, and its report.
