# Design

What exists, how it is built, and why. This file describes the code as it is; plans are
in `STATUS.md`, and the `.mmb` format is in `MMB-NOTES.md`.

## Modules

| Module | Contents |
| ------ | -------- |
| `Whitehead/Mm0/Syntax.lean` | the syntax tree of a `.mm0` file, source spans, `ParseError` |
| `Whitehead/Mm0/Lexer.lean` | bytes → tokens; line/column and error formatting |
| `Whitehead/Mm0/Parser.lean` | tokens → statements (the grammar of `mm0.md`) |
| `Whitehead/Mm0/Print.lean` | statements → normalized `.mm0` text |
| `Main.lean` | the command line: `dump`, `bench`; `verify` and `prove` are stubs |
| `tests/Tests/Harness.lean` | a counting test harness (`check`, `checkEq`, `skip`) |
| `tests/Tests/Mm0/Parser.lean` | lexer and parser tests on hand-written snippets |
| `tests/Tests/Mm0/Corpus.lean` | the parser over the `.mm0` files of the MM0 repository |
| `tests/fixtures/questions/` | hand-assembled `.mmb` files behind the open questions |
| `scripts/build-oracles.sh` | builds `mm0-c` into `.tools/bin` |

There is no `.mmb` reader yet. Its intended shape is section 10 of `MMB-NOTES.md`.

## The `.mm0` front end

### Two parsing levels

`mm0.md` has a primary grammar (statements) and a secondary one (the contents of
`$ ... $`, which depends on the notations declared in the file). The code that exists is
the primary level: a math string is kept in the tree as its raw text and its span. The
secondary parser will be a separate module that takes the statements in order, maintains
the notation environment and turns each `MathString` into an expression tree.

### Lexing on bytes

The lexer reads a `ByteArray`, not a `String`.

- The grammar is ASCII outside math strings, so a byte offset is a source position and
  nothing needs decoding until a lexeme is cut out.
- It avoids `String.Pos` arithmetic entirely.
- Illegal bytes (tab, carriage return, non-ASCII, NUL) are detected where they stand and
  reported by name.

A math string's text must be valid UTF-8, because it becomes a `String`.

### A pull lexer, no token array

`Lexer.nextToken src pos` returns the token that starts at or after `pos`. The parser
holds one token of lookahead and asks for the next one when it consumes it. No array of
tokens is built: a token is up to four heap objects, and the `.mm0` side of the set.mm
translation will be much larger than the example files. For the same reason the parser's
entry point is `parseStmt?`, one statement at a time; `parse` (the whole file as an
array) is a loop around it. A verifier that walks the `.mm0` file in step with the `.mmb`
statements, as `mm0-c` does, can use `parseStmt?` and drop each statement after checking
it.

### The parser monad

`ParserM = EStateM ParseError ParserState`, with the state being the source, the
lookahead token and the end of the last consumed token (for statement spans).

- `EStateM` compiles to a function from state to a result, without an `Except` or a pair
  per step.
- `advance`, the only function that changes the state, is written as that function
  directly rather than with `get`/`set`. With `get`, the old state would still be
  referenced while the new one is built, and the update could not happen in place.
- The recursive functions are `partial def`: they are loops over the input, and the brief
  says not to spend effort on termination proofs for this kind of code.

Errors are a byte offset and a message; `ParseError.format` turns that into
`file:line:col: error: ...` with the source line and a caret. Error messages say what was
expected and what was found.

### One binder parser

The grammar has four binder productions (`type-binder`, `formula-type-binder`,
`dummy-binder`, and the binders of `notation`). They differ only in what they allow, so
there is one function with a context argument (`BinderCtx`): formulas only in the `(...)`
binders of `axiom`/`theorem`; `.x` dummies only in `def`; `_` in a `{...}` binder only in
`def`.

### Where we follow `mm0.md`, and where we do not

The primary parser implements the grammar of `mm0.md` literally, with one exception. The
`mm0-c` column is that verifier's own `.mm0` parser (`mm0-c/parser.c`); each row was
checked by running `mm0-c` on a small file pair.

| Input | `mm0.md` | `mm0-c` | This parser |
| ----- | -------- | ------- | ----------- |
| `def all: type > term;` (arrows in a `def`) | no: a single `type` | accepts | **accepts** — `examples/hol.mm0` uses it |
| `strict pure sort s;` (modifiers out of order) | no | accepts | rejects |
| `prec 01` (leading zero) | no | accepts | rejects |
| `term b {_: s}: s;` (`_` in a `{...}` binder outside `def`) | no | accepts | rejects |
| `input ...;`, `output ...;` | optional | rejects | parses |
| a comment ended by the end of the file | no: needs `\n` | accepts | accepts |
| a NUL byte inside a math string | allowed by `[^$]*` | rejects | rejects |
| `import "file";` | not in the grammar | rejects | rejects |

The MM0 repository's own tests (`tests/mm0_mmu/fail/bad-sort*`, `bad-int5`) expect the
out-of-order modifiers and the leading zero to be rejected, which is why the grammar is
followed there rather than `mm0-c`. This matters for phase 2: "every `.mmb` accepted by
`mm0-c` is accepted by us" is stated for proof files, but the rows where `mm0-c` accepts
and we reject are cases where the two would disagree on a *specification* file. It is an
open question in `STATUS.md`.

`import` is an `mm0-rs` extension, resolved by `mm0-rs join`; nine of the example files
start with it. The corpus test overwrites those lines with spaces so that the rest of the
file is parsed.

The grammar accepts some things that are wrong for reasons the primary parser does not
look at, and that the later stages must check: unknown sorts and terms, a variable
declared twice, dependencies on variables that are not bound, a bound variable given
dependencies, a variable binder after a hypothesis, precedences out of range.

### Printing

`printStmts` writes the tree back as `.mm0`, one statement per line, math strings
verbatim. It is the `dump` output for `.mm0` files and the round-trip check: printing a
parsed file and parsing the result must give text that prints identically.

## Testing

`lake test` builds and runs the `test` executable.

- Snippet tests are self-contained. A rejection test marks the expected error position
  with `@` in the source and names a fragment of the expected message, so both where and
  what are checked.
- Corpus tests need a checkout of the MM0 repository, named by `MM0_REPO`; without it they
  are reported as skipped. Every `.mm0` file there must parse and round-trip; every file
  of `tests/mm0_mmu/fail` must be rejected, except the one that is grammatical and wrong
  for a later reason.
- `tests/fixtures/questions/gen.py` assembles small `.mmb` files by hand. They are the
  evidence for the disagreements in `MMB-NOTES.md` and will become differential tests.

## The prover

Nothing exists yet. Phase 3 is a port of Russell's engine (`CLAUDE.md`, "Russell — the
reference implementation of the prover"); its data structures will be described here from
the Flow9 source when that phase starts.
