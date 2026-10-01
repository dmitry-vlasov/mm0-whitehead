# Status

Last updated: 2026-10-01.

## Phase

**Phase 1 — readers**, in progress.

| Deliverable | State |
| ----------- | ----- |
| `docs/MMB-NOTES.md` | written; **waiting for review** before the `.mmb` reader is started |
| `.mm0` primary parser (statements, binders, source positions, error messages) | done, tested |
| `.mm0` secondary parser (math strings, notations, coercions) | not started |
| `.mmb` reader | not started (gated on the review above) |
| `dump` for `.mm0` | done (normalized `.mm0` text) |
| `dump` for `.mmb` | not started |
| Phase 1 acceptance | not reached |

## What passes

`MM0_REPO=/path/to/mm0 lake test` — 166 checks, 0 failures:

- 110 lexer and parser checks on hand-written snippets, 62 of them malformed inputs with
  the error position and message checked;
- the parser over 31 `.mm0` files of the MM0 repository (346,421 bytes, 3,159
  statements), each of which also round-trips through the printer;
- 25 files of `tests/mm0_mmu/fail`: 24 rejected, and `blank_binder_alias.mm0` accepted
  because it is grammatical (it is wrong for a reason phase 2 checks).

Without `MM0_REPO` the corpus part is skipped and reported as such.

Parser speed: about 50–60 MB/s on `examples/peano.mm0` (`mm0-whitehead bench`); the files
are too small for this to be a careful measurement.

## Waiting for answers

1. **`docs/MMB-NOTES.md`** — review, as the brief asks. Section 9 lists nine points where
   the spec and `mm0-c` disagree (D1–D9) and three questions for phase 2 (Q1–Q3), each
   with a proposal. The one that matters most:
   - **D1**: `mm0-c` accepts a proof that the MM0 semantics reject (and that derives a
     statement which is not valid). The brief asks both to follow the formalization and
     to agree with `mm0-c` on every file; here that is impossible. Evidence:
     `tests/fixtures/questions/bound_arg_vars.{mm0,mmb}`.
2. **`.mm0` files: `mm0.md` or `mm0-c`?** The parser follows the grammar of `mm0.md`, with
   one extension that the example files need (arrows in `def`). `mm0-c` accepts some
   inputs the grammar forbids (modifier order, leading zeros, `_` in `{...}`) and rejects
   `input`/`output`. Table in `docs/DESIGN.md`. Which is the reference for phase 2?
3. **`import "file";`** — an `mm0-rs` extension used by 9 of the example files, not in
   `mm0.md`, rejected by `mm0-c`. Should our reader support it (and do the joining), or
   should we only read files that have been through `mm0-rs join`?
4. **Toolchains needed for the phase 1 acceptance corpus**, both of which would install
   something outside this repository, so neither was done:
   - `mm0-rs` (to compile `examples/*.mm1` into `.mmb`) does not build with the installed
     Rust: stable 1.93.1 lacks a library feature it uses, and the installed nightly
     (2025-05-11) is too old. It needs a newer stable (`rustup update stable`, or a
     separate newer toolchain).
   - The set.mm translation needs `mm0-hs from-mm`, which builds with `stack` on
     `lts-13.27` (GHC 8.6.5, not installed; `stack` would download it). `set.mm` itself is
     at `~/dev/math/set.mm`.

## Available now for testing

- `mm0-c` and `mm0-c-np`, built by `scripts/build-oracles.sh` into `.tools/bin`.
- Three real `.mm0`/`.mmb` pairs that `mm0-c` accepts:
  `examples/hol.mm0` + `mm0-js/test/hol.mmb`,
  `examples/peano.mm0` + `mm0-js/test/peano.mmb`,
  `examples/tutorial/02-mm0-intro.mm0` + `examples/tutorial/03-mm1-intro.mmb`.
- The mutated files of `tests/mmb/{pass,fail,fail-index}` in the MM0 repository, which
  need `mm0-c-np`.

## Next steps

1. After the review: the `.mmb` reader as described in `MMB-NOTES.md` section 10, tests
   first, then `dump` for `.mmb`.
2. The secondary parser for math strings (delimiters, `prefix`/`infix`/`notation`,
   coercions), with its own tests.
3. The phase 1 acceptance run over all example pairs and the set.mm translation, once
   the toolchains in point 4 are settled.
