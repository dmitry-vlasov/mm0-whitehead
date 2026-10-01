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
| `Whitehead/Mm0/Env.lean` | the elaborated specification: sorts, terms, statements, expression trees |
| `Whitehead/Mm0/Math.lean` | the secondary parser: tokens, notations, coercions, formulas |
| `Whitehead/Mm0/Elab.lean` | statements → `Env` |
| `Whitehead/Mmb/Types.lean` | the data of a `.mmb` file: tables, commands, statements, patterns |
| `Whitehead/Mmb/Reader.lean` | opening a `.mmb` file; decoding binders, unify streams and proof bodies on demand |
| `Whitehead/Mmb/Encode.lean` | command streams back to bytes |
| `Whitehead/Mmb/Dump.lean` | a `.mmb` file as text |
| `Whitehead/Verify/Machine.lean` | the proof stack machine: store, stack, heap, unification, one rule per command |
| `Whitehead/Verify/Check.lean` | the statements of a proof file: binders, proof body, what must hold at its end; `checkProofs` |
| `Whitehead/Verify/Spec.lean` | a proof file against a specification: `matchSpec` |
| `Main.lean` | the command line: `dump`, `join`, `verify`, `bench`; `prove` is a stub |
| `tests/Tests/Harness.lean` | a counting test harness (`check`, `checkEq`, `skip`) |
| `tests/Tests/Mm0/Parser.lean` | lexer and parser tests on hand-written snippets |
| `tests/Tests/Mm0/Load.lean` | `import` resolution on `tests/fixtures/imports` |
| `tests/Tests/Mm0/Elab.lean` | formulas, notations and declarations on hand-written specifications |
| `tests/Tests/Mm0/Corpus.lean` | the parser and loader over the `.mm0` files of the MM0 repository |
| `tests/Tests/Mm0/Pairs.lean` | every elaborated statement against its counterpart in a `.mmb` file |
| `tests/Tests/Mmb/Reader.lean` | the reader on two small files, and on corruptions of one of them |
| `tests/Tests/Mmb/Corpus.lean` | the reader over real `.mmb` files, with the round trip |
| `tests/Tests/Verify/Proofs.lean` | the proof checker on `small.mmb` and on the disputed files |
| `tests/Tests/Verify/Cases.lean` | one proof file per rule, with the verdicts of `mm0-rs` and mm0-c |
| `tests/Tests/Verify/Spec.lean` | `matchSpec` on `small.mmb` against altered specifications |
| `tests/Tests/Verify/Corpus.lean` | the proof checker over real `.mmb` files |
| `tests/Tests/Mutate/Engine.lean` | mutations of a proof file, from a seed |
| `tests/Tests/Mutate/Main.lean` | `lake exe mutate`: our verdict against that of `mm0-rs` on mutants |
| `tests/fixtures/mmbasm.py` | a hand assembler for small `.mmb` files, used by the `gen.py` scripts |
| `tests/fixtures/mmb/` | `small.mmb`: a valid file with one of everything, and its expected dump |
| `tests/fixtures/disputed/` | hand-assembled `.mmb` files on which the sources disagree |
| `tests/fixtures/verify/` | hand-assembled `.mmb` files, one per rule of the verifier, and `cases.tsv` with the expected verdicts |
| `scripts/build-oracles.sh` | builds `mm0-rs`, `mm0-c` and `mm0-hs` into `.tools/bin` |
| `scripts/build-corpus.sh` | builds the `.mm0`/`.mmb` pairs for acceptance testing into `.tools/corpus` |
| `scripts/mutation-campaign.sh` | runs the mutation campaigns of the phase 2 acceptance test |

## The `.mm0` front end

### Two parsing levels

`mm0.md` has a primary grammar (statements) and a secondary one (the contents of
`$ ... $`, which depends on the notations declared in the file). The primary parser keeps
a math string in the syntax tree as its raw text and its span. The elaborator then takes
the statements in order, maintains the notation environment, and turns each math string
into an expression tree with the secondary parser.

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

### Math strings

`Math.lean` is "Secondary parsing" of `mm0.md`.

- **Tokens.** A math string is split at whitespace, after every left delimiter and before
  every right delimiter. `(` and `)` are tokens only if that splitting produces them, so
  a specification that wants `(a)` to work declares them as delimiters.
- **The grammar, exactly.** Parsing is precedence climbing in which every parsed
  expression carries its *level*, the precedence of its outermost construct: `max` for a
  variable, a parenthesized expression and a term without arguments; 1024 for a term
  applied to arguments; the notation's precedence for a notation. An infix operator at
  precedence `q` is taken only if the left operand's level is at least `q` (left
  associative) or `q + 1` (right associative), which is what the productions
  `expression(q) -> expression(q) OP expression(q+1)` and
  `expression(q+1) OP expression(q)` say. `mm0-rs` and mm0-c do not track the level of
  the left operand; their loops agree with the grammar as long as no precedence level
  has both a left and a right associative operator, and accept strings the grammar does
  not derive otherwise.
- **Terms take as many arguments as they have.** `f a b` reads exactly the arity of `f`
  arguments, each at `max`, as the production `FUNC expression(max){n}` says (`mm0-rs`
  reads all that follow and checks the count later; the valid inputs are the same).
- **A notation constant is never read as a name.** If a token is a declared constant, it
  is that constant, even where a variable or term of the same spelling would fit; this
  is the behaviour of `mm0-rs`. A token may be both a prefix and an infix constant, at
  one precedence.
- **Typing on the way.** Each argument is checked against the binder it goes into when
  the term is built. For a regular binder a coercion is inserted if the sorts differ.
  For a bound binder the argument must be a bound variable of that sort (a parenthesized
  variable is still a variable, as in the formal specification). A whole formula is then
  coerced to the sort it must have: the result sort for a `def`, some provable sort for
  a hypothesis or conclusion.
- **Coercions** are kept closed under composition: adding `t: s1 > s2` adds a path from
  everything that reaches `s1` to everything reachable from `s2`. A cycle, two paths
  between the same sorts, or two provable sorts reachable from one sort are errors at
  the declaration, as in `mm0-rs`. (`mm0-rs` and mm0-c do not compose a path that goes
  through both a predecessor of `s1` and a successor of `s2`; this code does.)

Tokens are cut out as strings, one allocation each, and looked up in hash maps. That is
the main cost of elaboration today: `setmm.mm0` (20 MB) loads and elaborates in 0.94 s,
of which parsing the statements is 0.20 s. If phase 2 needs it faster, this is where to
look first.

### Elaboration

`Elab.lean` turns statements into an `Env` (`Env.lean`): the sorts, terms, axioms and
theorems in order, with binders resolved (sort, bound or regular, dependencies as indices
of variables) and formulas as `Expr` trees over variable and term indices. This is the
environment of the formal specification (`Elaborate` in `mm0.mm0`), with names kept.
Terms are numbered in the order of the specification; a proof file numbers its local
definitions too, so the two numberings differ and have to be mapped.

Statements are elaborated one at a time against what was declared before
(`Elab.elabStmt`), so the elaborator can also be driven statement by statement.

What is checked: names (sorts, terms and theorems declared once; variables once per
declaration), the shape of binders (variables before hypotheses; dependencies only on
bound variables of earlier binders; none on a bound variable or a dummy), arities, sorts
and coercions in formulas, and the validity of notation declarations. What is left to
the verifier: the conditions of a well-formed environment (`strict`, `pure`, `free`, the
free variables of a definition).

A Lean detail that matters at this size: the functions that add a declaration take the
state apart with a pattern match and build a new one (`ElabState.pushThm`). Written as
`{ st with env := { st.env with thms := st.env.thms.push t } }` the array would be shared
at the time of the `push` and copied each time, which is quadratic over 49,156 theorems.

Where the sources differ on elaboration:

| Point | `mm0.md` | formal spec | `mm0-rs` | Here |
| ----- | -------- | ----------- | -------- | ---- |
| precedence of a term application | 1024; arguments at `max` | the comparison in `ptCheckFunc` is the other way round | as `mm0.md` | as `mm0.md` |
| a term without arguments | — | at 1024 like any application | at `max` | at `max` (also what mmb.md says for printing) |
| several anonymous variables (`_`, arrows) | allowed | `lookupVar` treats `_` as a name, so a second one fails | allowed | allowed |
| a variable binder after a hypothesis | grammar allows it | rejected | rejected | rejected |
| a token that is both prefix and infix | "must not be shared" | allowed | allowed | allowed |
| a coercion that creates a second path | graph must stay a forest | allowed; a formula with two parses fails | error at the declaration | error at the declaration |
| the binders of a `notation` | "annotated with types" | used for the names only | number checked | number checked |
| precedence values | at least up to 2046 | any number | below 2^32 | any number |
| `def` keyword in the grammar | `def` | `parseDef` asks for the token `theorem` | `def` | `def` |

The rows where the formal specification stands alone (the inverted comparison, `_`, the
`theorem` token) read like slips in it; in each of them `mm0.md` and `mm0-rs` agree with
each other and are followed.

## The `.mmb` reader

The format and what the reader accepts are in `MMB-NOTES.md` (sections 1–5, 7 and 10).
What is specific to the Lean code:

- **The file stays a `ByteArray`.** `MmbFile` holds the bytes and what is cheap and small:
  the header, one structure per table entry and per statement, and the names. Binders,
  unify streams and proof bodies are decoded by accessor functions when asked for. The
  verifier does not ask for them as arrays at all: it steps through the bytes.
- **`Arg` is a structure around one `UInt64`**, which Lean represents as the bare scalar,
  with `bound`, `sort` and `deps` as bit operations. 64-bit words are assembled with
  `UInt64` operations, not through `Nat`, so that a set top bit (every bound variable)
  does not create a big number.
- **`readCmd` returns an `Except` of a triple** and is `@[inline]`. That is fine for the
  reader, which builds arrays anyway. The verifier's loops do not use it: they check the
  bounds once and read the opcode and the data with `cmdSize` and `cmdData`
  (`Verify/Machine.lean`), which return plain numbers.
- **Bytes are put together as machine integers** (`u16`, `u32`, `word64`). A left shift
  of a `Nat` is a call into the big number library even when the result is small.
- **Errors are an offset and a message**, as for `.mm0`; the reader stops at the first.
- The stream decoders are `partial def` loops over the bytes; `readPattern` recurses on
  the term structure of a unify stream, which is as deep as the formula it describes.

`Encode.lean` exists because the acceptance test needs the inverse of the stream decoders
(decode, encode, compare with the original bytes). It writes the shortest encoding, as
`mm0-rs` does. The prover's `.mmb` emission will build on it.

`dump` writes line by line through a callback rather than building a string: the dump of
the set.mm translation is 15.6 million lines (390 MB), written in 3.5 s.

## The verifier

`verify spec.mm0 proof.mmb` does two things, in two modules that do not know each other:

1. `checkProofs` (`Verify/Check.lean`, on top of `Verify/Machine.lean`): the proof file
   is valid on its own. Every statement's binders are well-formed, its proof body runs
   on the stack machine, and what the body leaves is the statement that the tables
   declare. This is what `mm0-rs compile file.mmb` checks, and `verify proof.mmb` alone
   stops here.
2. `matchSpec` (`Verify/Spec.lean`): the public statements of the proof file are, in
   order, the declarations of the specification.

The rules are those of `MMB-NOTES.md` section 6, with the decisions of its section 9
where the sources differ. The comments in the code name the rule each function
implements and, where there is one, the definition of the formal semantics it follows.

### Representation

The checking logic is plain; the speed is in how the data are laid out.

- **Commands are read from the bytes of the file**, never decoded into values.
- **The store** is one `Array Nat` that holds every expression of the statement being
  checked; it is emptied for the next statement and keeps its memory. A node is the
  index of its first slot: `store[e]` is its type word, `store[e+1]` is `0` for a
  variable and `t + 1` for an application of term `t`, and the argument nodes follow.
- **Two expressions are equal when they are the same node.** That is the equality of
  the format (`mm0b.lean`, `mm0-rs`): a proof that builds the same term twice has two
  nodes, and must use `Ref` to mean the first one. There is no hash-consing and no
  structural comparison, so `Refl`, `URef` and the comparison of a saved conversion are
  one comparison of two numbers.
- **The type word** of a node is one number: bits 0–54 the bound variables it depends
  on, bits 55–61 its sort, bit 62 set for a bound variable. It is computed once, when
  the node is made. In a theorem the dependencies are the variables of the expression
  (the union over all arguments); in a definition they are its free variables.
- **A stack or heap element** is one number: the kind (expression, proof, conversion,
  obligation) in the low two bits, then one or two node indices of 30 bits.
- All arrays therefore hold small numbers, which Lean stores unboxed, and a command
  allocates nothing but array slots.

### The loop, and what the Lean compiler does with it

The first version kept the whole state in one record of 12 fields and wrote every
command in the state monad. It verified the set.mm translation's proofs in 1.8 s; the
budget for the whole verification is 2.6 s. A profile (`valgrind --tool=callgrind`; `perf`
is not permitted on this machine) showed 2,400 instructions per proof command, and three
causes that have nothing to do with the checking itself:

| Change | Proofs of `setmm.mmb` | Instructions |
| ------ | --------------------- | ------------ |
| first version | 1.80 s | 38.2 G |
| masks and shifts on `UInt64` instead of `Nat` literals | 1.36 s | 28.7 G |
| the loop on separate arrays; byte reads on `UInt32` | 0.55 s | 12.1 G |

- **A `Nat` literal of 2^32 or more inside a function is rebuilt each time it runs**,
  by a call that parses its decimal digits. The masks of the type word were such
  literals. The words are still stored as `Nat`, but they are taken apart with `UInt64`
  operations (`Ty` and `El` in `Machine.lean`), whose literals are machine constants.
- **`Nat` shifted left always goes through the big number library.** The 16- and
  32-bit operands of commands were assembled that way.
- **A record is updated in place only in a narrow case.** For `{ m with stack :=
  m.stack.push x }` the compiler reuses the record if it is not shared, and avoids
  touching the reference counts of the other fields only if the reads of the fields
  directly precede the update, in the same basic block (the pass `ExpandResetReuse`
  looks for exactly that pattern). With a test of `m` in between — and a command always
  tests before it updates — every field is incremented and decremented again. In the
  loop itself, where the record was also updated for the position of the command, the
  compiled code freed the record and allocated a new one for every `Ref`.

So the loop over the commands of a proof (`run`) carries the store, the stack, the heap
and the two arrays of unification as separate variables, each with one owner: a push or
a pop is then done in place, with no record around it. What the loop calls is written to
fit: a function either reads arrays and returns a number (`argsFault`, `argsVars`,
`argsFree`, `boundDeps`), or takes one array and returns it (`argsToStore`,
`argsToUheap`, `pushArgs`). A failed check of arguments is reported as a number (which
argument, which rule), and the message is made from it only when needed. `unify` works
on its two arrays as loop variables too, and returns them in a small record once per
unification. The record `Machine` remains for what happens between statements and for
the rare commands (`stepOther`: everything but `Ref`, `Term` and `Thm`, which are 99% of
the commands of set.mm); those are written in the state monad, where clarity costs
nothing measurable.

The rules did not change in this rewrite, and their order of checks did not either. The
scratch array of "dependencies of the bound arguments so far" went away: `boundDeps`
computes the same union from the binders and the arguments on the stack.

`partial def` is used for all loops: they run over the bytes of a file, and nothing
would be gained by proving that they end.

### Errors

A failed check is a message, the file offset of the command or statement, and the index
of the statement (`VerifyError`); it is printed as `file:0x<offset>: error: in theorem
foo: <message>`. The verifier stops at the first error.

### Against the specification

`matchSpec` walks the statements of the proof file and the declarations of the
elaborated specification side by side. Local definitions and theorems of the proof file
are skipped; everything else must be the same kind of declaration with the same
content: the modifiers of a sort, the binders and return type of a term bit for bit,
and each formula as a tree, the expression elaborated from the `.mm0` text against the
unify stream of the proof file. A definition may have its value in the proof file only.
Names are not compared — the index is not part of what is proved — and the term numbers
of the two sides differ by the local definitions, so a map from one to the other is
built on the way. This is `env.extend` of `mm0.lean`. `mm0-rs` has no counterpart; mm0-c
has one, in `parser.c`.

Time on the set.mm translation (49,156 axioms and theorems), one run:

| Step | Time |
| ---- | ---- |
| load and elaborate `setmm.mm0` | 0.89 s |
| check the proofs of `setmm.mmb` | 0.56 s |
| match the two | 0.35 s |
| total | 1.80 s |

mm0-c does the same in 0.26 s. Half of our time is the `.mm0` front end, which builds a
syntax tree and an environment where mm0-c compares the text with the proof file as it
reads it. That tree is what the prover will work on, so the front end stays as it is.

## Testing

`lake test` builds and runs the `test` executable, from the package root.

- Snippet tests are self-contained. A rejection test marks the expected error position
  with `@` in the source and names a fragment of the expected message, so both where and
  what are checked.
- Import tests run on the small files in `tests/fixtures/imports`.
- Elaborator tests put a formula on top of a small signature and compare the resulting
  tree, as an s-expression, with the expected one; rejections are checked for position
  and message as above.
- The pair test is the elaborator's strongest check. For a `.mm0`/`.mmb` pair it compares
  every statement elaborated from the `.mm0` text with the statement the proof file
  declares at the same place: modifiers of sorts, binders and return types bit for bit,
  and every formula against the tree of its unify stream. The two were produced
  independently (ours by parsing notation; theirs by `mm0-rs` or `mm0-hs`). It runs on
  the fixtures of this repository, on the pairs of the MM0 repository, and on the built
  corpus including the set.mm translation.
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
- `tests/fixtures/verify/gen.py` assembles one proof file per rule of the verifier: 48
  files, each valid or invalid in one known way. `cases.tsv` records for each our
  verdict (a fragment of the error message), the verdicts of `mm0-rs` and of mm0-c, and,
  where `mm0-rs` differs from us, the point of section 9 that explains it. The test
  checks our verdict always and the other two when the tools are built. This is the
  differential test on hand-written cases.
- The verifier corpus test runs `checkProofs` over the same proof files as the reader
  corpus test. Every valid one must be accepted; the mutants of the MM0 repository that
  the reader lets through must be rejected, each with its own message.
- `matchSpec` is tested on `small.mmb` against its specification with one thing changed
  at a time (18 cases: what may differ, and what may not), and by the pair test above.
- `lake exe mutate FILE.mmb --count N --seed S` makes N mutants of a valid proof file
  (a flipped bit in a chosen part of the file, two proof commands swapped, an opcode or
  an operand altered, a broken binder, a truncation), checks each with our verifier and
  with `mm0-rs compile`, and compares. A difference must be one of the known ones of
  section 9, recognized from our error message; anything else is reported and the
  mutant kept. `scripts/mutation-campaign.sh` runs the campaigns of the acceptance
  test. They run with `LEAN_ABORT_ON_PANIC=1`, so that an index out of bounds in the
  verifier would be a crash and not a message. With `--mm0-c PATH` the mutants that
  both accept are also shown to mm0-c.

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
