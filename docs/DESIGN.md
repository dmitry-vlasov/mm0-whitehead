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
| `Whitehead/Mm0/Load.lean` | a specification with its `import`s resolved |
| `Whitehead/Mmb/Types.lean` | the data of a `.mmb` file: tables, commands, statements, patterns |
| `Whitehead/Mmb/Reader.lean` | opening a `.mmb` file; decoding binders, unify streams and proof bodies on demand |
| `Whitehead/Mmb/Encode.lean` | command streams back to bytes |
| `Whitehead/Mmb/Dump.lean` | a `.mmb` file as text |
| `Main.lean` | the command line: `dump`, `join`, `bench`; `verify` and `prove` are stubs |
| `tests/Tests/Harness.lean` | a counting test harness (`check`, `checkEq`, `skip`) |
| `tests/Tests/Mm0/Parser.lean` | lexer and parser tests on hand-written snippets |
| `tests/Tests/Mm0/Load.lean` | `import` resolution on `tests/fixtures/imports` |
| `tests/Tests/Mm0/Corpus.lean` | the parser and loader over the `.mm0` files of the MM0 repository |
| `tests/Tests/Mmb/Reader.lean` | the reader on two small files, and on corruptions of one of them |
| `tests/Tests/Mmb/Corpus.lean` | the reader over real `.mmb` files, with the round trip |
| `tests/fixtures/mmbasm.py` | a hand assembler for small `.mmb` files, used by the `gen.py` scripts |
| `tests/fixtures/mmb/` | `small.mmb`: a valid file with one of everything, and its expected dump |
| `tests/fixtures/disputed/` | hand-assembled `.mmb` files on which the sources disagree |
| `scripts/build-oracles.sh` | builds `mm0-rs`, `mm0-c` and `mm0-hs` into `.tools/bin` |
| `scripts/build-corpus.sh` | builds the `.mm0`/`.mmb` pairs for acceptance testing into `.tools/corpus` |

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

The text of a math string, and of a string literal, must be valid UTF-8, because it
becomes a `String`.

### A pull lexer, no token array

`Lexer.nextToken src pos` returns the token that starts at or after `pos`. The parser
holds one token of lookahead and asks for the next one when it consumes it. No array of
tokens is built: a token is up to four heap objects, and the `.mm0` side of the set.mm
translation is 20 MB. For the same reason the parser's entry point is `parseStmt?`, one
statement at a time; `parse` (the whole file as an array) is a loop around it. A verifier
that walks the `.mm0` file in step with the `.mmb` statements can use `parseStmt?` and
drop each statement after checking it.

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
binders of `axiom`/`theorem`; `.x` dummies only in `def`.

### What the parser accepts, and by whose authority

The reference for `.mm0` files is `mm0.md` together with the formal specification
(`examples/mm0.mm0`, which contains a lexer, a grammar and an elaborator for MM0, written
in MM0). `mm0-rs` is not the reference here: its parser is the parser of the larger MM1
language and accepts more. The table lists every point found where the three differ. The
`mm0-rs` column was checked by running `mm0-rs compile` on a small file for each row.

| Input | `mm0.md` | formal spec | `mm0-rs` | This parser |
| ----- | -------- | ----------- | -------- | ----------- |
| `import "file";` | no | no | accepts | **accepts** — extension, see below |
| `def all: type > term;` (arrows in a `def`) | no: a single `type` | no | accepts | **accepts** — extension, see below |
| `strict pure sort s;` (modifiers out of order) | no | no | accepts | rejects |
| `prec 01` (leading zero) | no | no | accepts | rejects |
| a comment ended by the end of the file | no: needs `\n` | no | accepts | rejects |
| `term a (.x: s): s;` (dummy outside `def`) | no | no (elaboration) | accepts | rejects |
| `term b {_: s}: s;` (`_` in `{...}` outside `def`) | no | yes | accepts | accepts |
| a NUL byte inside a math string | allowed by `[^$]*` | allowed | rejects | accepts |
| `input ...;`, `output ...;` | optional | parsed, but such a file has no valid elaboration | `output string` only | parses |
| a variable binder after a hypothesis binder | grammar allows it | no (elaboration) | rejects | parses; for the elaborator to reject |

Two extensions go beyond both references, because the example files need them:

- **`import "file";`** is an `mm0-rs` extension, and nine of the example specifications
  use it. It is a statement in the syntax tree (`StmtKind.importFile`), and
  `Whitehead.Mm0.load` resolves it. The string literal has the escapes of `mm0-rs`
  (`\\`, `\"`, `\n`, `\r`, `\xHH`); an unknown escape is an error here and a warning there.
- **Arrows in a `def`** (`def all: type > term;`) are used by `examples/hol.mm0`. Neither
  `mm0.md` nor the formal specification has them; `mm0-rs` and mm0-c accept them.

Where `mm0.md` and the formal specification disagree with each other (the `_` row), the
formal specification is followed.

The grammar accepts some things that are wrong for reasons the primary parser does not
look at, and that the elaborator must check: unknown sorts and terms, a variable declared
twice, dependencies on variables that are not bound, a bound variable given dependencies,
a variable binder after a hypothesis, precedences out of range.

### Imports

`load path` returns a `Spec`: the files that were read and one flat list of statements,
each tagged with the file it stands in, with no `import` left. The meaning is that of
`mm0-rs join`: textual inclusion at the place of the statement; the path is relative to
the directory of the importing file; a file that has already been included is skipped.
Files are identified by their canonical path (`IO.FS.realPath`).

One deliberate difference: every import cycle is an error. `mm0-rs join` reports only a
cycle that goes through the file it started from and silently skips the others (`mm0-rs
compile` reports them all).

Errors keep their place: a parse error in an imported file is reported in that file, and
an unreadable import or a cycle is reported at the string literal of the `import`.

The loader keeps the whole statement list in memory. When the verifier needs to stream
(one statement at a time across files) it can do so with the same pieces — `parseStmt?`
and a stack of open files — but nothing needs that yet.

### Printing

`printStmts` writes the tree back as `.mm0`, one statement per line, math strings
verbatim. It is the `dump` output for `.mm0` files, the `join` output, and the round-trip
check: printing a parsed file and parsing the result must give text that prints
identically.

## The `.mmb` reader

The format and what the reader accepts are in `MMB-NOTES.md` (sections 1–5, 7 and 10).
What is specific to the Lean code:

- **The file stays a `ByteArray`.** `MmbFile` holds the bytes and what is cheap and small:
  the header, one structure per table entry and per statement, and the names. Binders,
  unify streams and proof bodies are decoded by accessor functions when asked for. A
  verifier will not ask for them as arrays at all: it will step through the bytes with
  `Reader.readCmd`.
- **`Arg` is a structure around one `UInt64`**, which Lean represents as the bare scalar,
  with `bound`, `sort` and `deps` as bit operations. 64-bit words are assembled with
  `UInt64` operations, not through `Nat`, so that a set top bit (every bound variable)
  does not create a big number.
- **`readCmd` returns an `Except` of a triple** and is `@[inline]`. That is fine for the
  reader, which builds arrays anyway. Whether the verifier's inner loop can use it
  without allocating is a phase-2 measurement, not something assumed here.
- **Errors are an offset and a message**, as for `.mm0`; the reader stops at the first.
- The stream decoders are `partial def` loops over the bytes; `readPattern` recurses on
  the term structure of a unify stream, which is as deep as the formula it describes.

`Encode.lean` exists because the acceptance test needs the inverse of the stream decoders
(decode, encode, compare with the original bytes). It writes the shortest encoding, as
`mm0-rs` does. The prover's `.mmb` emission will build on it.

`dump` writes line by line through a callback rather than building a string: the dump of
the set.mm translation is 15.6 million lines (390 MB), written in 3.5 s.

## Testing

`lake test` builds and runs the `test` executable, from the package root.

- Snippet tests are self-contained. A rejection test marks the expected error position
  with `@` in the source and names a fragment of the expected message, so both where and
  what are checked.
- Import tests run on the small files in `tests/fixtures/imports`.
- Corpus tests need a checkout of the MM0 repository, named by `MM0_REPO`; without it they
  are reported as skipped. Every `.mm0` file there must parse and round-trip; every file
  of `tests/mm0_mmu/fail` must be rejected, except the one that is grammatical and wrong
  for a later reason. If `mm0-rs` is available (`.tools/bin/mm0-rs`, or `MM0_RS`), the
  joined form of every file with imports is compared with `mm0-rs join`.
- Reader tests decode the file that `MMB-NOTES.md` section 8 annotates byte by byte and
  compare every decoded field with that listing; then they corrupt single bytes of it and
  check the offset and the message of each rejection. A second file, `small.mmb`, has an
  index, a definition with a dummy, hypotheses and a proof by conversion; its dump is
  compared with the checked-in `small.dump`.
- The `.mmb` corpus test runs over the proof files of the MM0 repository and of
  `.tools/corpus`: each must decode, every stream must re-encode to its original bytes,
  and the dump must run to the end. The mutants of `tests/mmb/` in the MM0 repository
  have a fixed expected verdict each (rejected by the reader, or left to the verifier).
- `tests/fixtures/disputed/gen.py` assembles small `.mmb` files by hand, one for each
  point on which the sources disagree about proof checking (`MMB-NOTES.md`, section 9).
  They are the regression tests for the verifier's deliberate differences from
  `mm0-rs` and mm0-c.

### External tools and the acceptance corpus

Neither is under version control; both are rebuilt by scripts.

- `scripts/build-oracles.sh` builds `mm0-rs` (the reference implementation), `mm0-c` (a
  second verifier and the speed yardstick) and, with `--with-hs`, `mm0-hs` (needed only
  to translate set.mm) into `.tools/bin`, without writing into the MM0 checkout.
- `scripts/build-corpus.sh` compiles every example that has a specification into
  `.tools/corpus/<name>.mmb` with its joined `<name>.mm0`, translates set.mm into
  `setmm.mm0`/`setmm.mmb`, and prints what `mm0-rs` and mm0-c say about each pair.

Two workarounds are needed for set.mm, both because `mm0-hs` is older than its
surroundings; the script documents them. It cannot read the double-quoted strings that
`$j` comments in set.mm now contain, so they are requoted in a copy. And it writes the
index in a layout that predates mmb.md, which `mm0-rs` rejects, so the index is removed
from the translated file. The names of the set.mm statements are still available from
`setmm.mm0`, where every one of them is declared.

## The prover

Nothing exists yet. Phase 3 is a port of Russell's engine (`CLAUDE.md`, "Russell — the
reference implementation of the prover"); its data structures will be described here from
the Flow9 source when that phase starts.
