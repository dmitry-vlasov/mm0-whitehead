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
| `Whitehead/Mmb/Write.lean` | a proof file with other proof bodies |
| `Whitehead/Prove/*.lean` | the prover: see "The prover", "Modules" |
| `Main.lean` | the command line: `dump`, `join`, `verify`, `bench`, `prove replay`, `prove search`, `prove db` |
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
| `tests/Tests/Prove/Util.lean` | a small language for the prover's tests, random expressions, a reference unifier on trees |
| `tests/Tests/Prove/Subst.lean`, `Unify.lean`, `Index.lean` | expressions and substitutions; unification and the index, also against the reference on random input |
| `tests/Tests/Prove/Engine.lean` | the engine on the logic fixture: database, replay, search, conditions on bound variables, answers |
| `tests/Tests/Mutate/Engine.lean` | mutations of a proof file, from a seed |
| `tests/Tests/Mutate/Main.lean` | `lake exe mutate`: our verdict against that of `mm0-rs` on mutants |
| `tests/fixtures/mmbasm.py` | a hand assembler for small `.mmb` files, used by the `gen.py` scripts |
| `tests/fixtures/mmb/` | `small.mmb`: a valid file with one of everything, and its expected dump |
| `tests/fixtures/disputed/` | hand-assembled `.mmb` files on which the sources disagree |
| `tests/fixtures/verify/` | hand-assembled `.mmb` files, one per rule of the verifier, and `cases.tsv` with the expected verdicts |
| `scripts/build-oracles.sh` | builds `mm0-rs`, `mm0-c` and `mm0-hs` into `.tools/bin` |
| `scripts/build-corpus.sh` | builds the `.mm0`/`.mmb` pairs for acceptance testing into `.tools/corpus` |
| `tests/fixtures/prove/` | `logic.mm1`, a small deductive system with proofs, and `logic.mmb` compiled from it by `mm0-rs` (`gen.sh`) |
| `scripts/mutation-campaign.sh` | runs the mutation campaigns of the phase 2 acceptance test |
| `scripts/search-baseline.sh`, `scripts/search-summary.py` | run and summarize the search test of phase 3 |

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

- The prover's parts are tested bottom up. Substitutions and unification have
  hand-written cases, and are compared on random input with a second unifier that is
  written on trees in the plainest way and shares no code with the port: 20,000 pairs of
  expressions and 5,000 sets of substitutions must give the same outcome, and a unifier
  that makes the expressions equal, is idempotent, and is as general as the reference
  one. The index is compared with unifying the given expression with each stored one,
  on 2,000 lookups among 400 expressions.
- The engine is tested on `tests/fixtures/prove/logic.mmb`: every proof of the file
  replays; breadth-first search finds 15 of its 16 theorems, none by a longer proof than
  the file's, and the file with the proofs found is valid; a condition on a bound
  variable is judged violated, settled or open in hand-made cases; a goal with a
  variable gets its answer. When the corpus is built, the first 6,000 statements of
  set.mm are replayed and the resulting file is verified.

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

The engine of Russell, ported from the Flow9 source, with MM0 as its deductive system.
What follows: what is ported from where; how MM0 maps onto the framework of
`docs/proof_search_algo.pdf` ("the paper"); every place where the Lean code does
something else than the source, and why; emission; the results of the two acceptance
tests. The questions that need an answer are at the end and in `STATUS.md`.

### Modules

| Lean module | Flow9 source | Contents |
| ----------- | ------------ | -------- |
| `Prove/Exp.lean` | `ru/src.flow` (`RuExp`), `ru/util/exp.flow` | expressions as flat arrays of nodes in prefix order, each application with the length of its arguments |
| `Prove/Subst.lean` | `ru/subst.flow` | `RuSubst`: `ruApplySubst`, `ruAdd2Subst`, `ruCompose`, `ruUnsafeCompose`, `ruMatchExp`, `ruMergeSubst`, `ruSplitSubs` |
| `Prove/Unify.lean` | `ru/unify/exps.flow` | `ruUnifyExps`, `ruUnifySubs` |
| `Prove/Index.lean` | `ru/index.flow`, `ru/unify/index.flow` | `RuIndex`, `ruSetIndex`, `ruIndexSubexpr`, `ruUnifyIndex` |
| `Prove/Db.lean` | `ru/prover/core/util.flow` | the assertions of a proof file as expressions, the task with its constants (`ruConstProverTask`), proofs of the file as trees of assertions |
| `Prove/Prod.lean` | `ru/unify/prod.flow`, `ru/unify/indexes.flow` | `ruUnifySubsProd`, `ruUnifyIndexes`: the tuples of substitutions that unify, without trying each |
| `Prove/Tree.lean` | `core/tree.flow` | the nodes of the tree, the proofs on them, `RuProofTree` |
| `Prove/Env.lean` | `core/env.flow` | `RuProverEnv` |
| `Prove/Proofs.lean` | `core/proofs.flow`, `core/tree.flow` | `ruAddProof`, `ruBuildPropProofs`, `ruBuildExpProofs`, `ruMakeProofTree` |
| `Prove/Forward.lean` | `core/forward.flow` | the forward front: `ruSeedForwardFront`, `ruApplyForward`, `ruExpandForwardProved`, `ruReverseJoin` |
| `Prove/Expand.lean` | `core/expand.flow` | `ruExpandHyp`, `ruExpandProp` with its join with the forward front; `ruProveProp` of `prove.flow` |
| `Prove/Prove.lean` | `core/prove.flow`, `core/controls.flow`, `tactics/breadth_first.flow`, `tactics/oracle.flow`, `ruRunForwardWave` | the loop, the strategy interface, the strategies (breadth first, forward, both in turn, replay of a known proof); closing and accepting a proof |
| `Prove/Emit.lean` | — | a proof tree as the proof body of a `.mmb` file |
| `Prove/Replay.lean` | — | the two acceptance tests as commands: `prove replay`, `prove search` |
| `Mmb/Write.lean` | — | a proof file with other proof bodies |

Not ported, each being a layer of its own in the source: proof fragments
(`fragment.flow`), the forward closure (`forward_closure.flow`), the variant-admission
hook, the seed hooks and the ordered wave of the forward front, statistics, concurrency,
and the tactic language.

### The engine

- **The proof variant tree.** Expression nodes (`HypNode`: `RuProverRoot`, `RuProverExp`)
  and assertion nodes (`PropNode`: `RuProverProp`) alternate. They are in two arrays and
  refer to each other by number; Russell has mutable vectors inside the nodes and
  pointers both ways. An assertion node carries the assertion and the unifier in two
  parts: `outer`, on the variables of the assertion, and `sub`, on the variables of the
  goal that the unification had to instantiate.
- **Upward pass** (`Expand.lean`). `expandHyp` unifies an expression node with the
  conclusions in the index, renames the variables of the assertion that the unifier left
  free with fresh ones, and makes an assertion node for each result, those that bind
  more first. `expandProp` makes the child expression nodes, the premises under the
  unifier, matches each with the premises of the task, and expands each child at once.
  So the leaves that a strategy chooses among are assertion nodes.
- **Downward pass** (`Proofs.lean`). `addProof`: when a child gets a new proof, the
  product of it with the proofs of the siblings is walked; for each tuple the most
  general unifier of their substitutions (`unifySubs`) is composed with the node's `sub`,
  the conditions on bound variables are checked, and the result is a proof of the
  assertion node. `buildPropProofs` and `buildExpProofs` carry new proofs to the parent,
  up to the root.
- **The proofs on the nodes** (`Proof`: `RuProverProof`) are the substitution proof trees
  of the paper, immutable as in Russell.
- **Forward** (`Forward.lean`). The mirror of `expandHyp`: a *fact* is unified with the
  hypotheses of the assertions, and their conclusions become facts. The front starts
  with the premises of the task and the assertions without hypotheses. An application
  takes the fact for one hypothesis and fills the others from the front; the proofs are
  joined by the same `addProof`. The two directions meet in *joins*: a fact proves the
  goal if the goal is an instance of it, and it proves every subgoal of the backward
  tree that it unifies with; the proof is put on the subgoal and carried down the tree
  like any other.
- **The loop** (`Prove.lean`) asks a strategy what to do next: expand these leaves
  (optionally with a restriction of what each premise may use), or advance the forward
  front by one wave. A strategy reads the tree; it does not change it. `breadthFirst`
  returns all leaves, which is the fair strategy of the completeness theorem;
  `forwardOnly` asks for waves; `bidirectional` for a round and a wave in turn; `oracle`
  returns the nodes that a known proof uses.
- **A proof at the root** is closed (see "Emission"), emitted and checked by our
  verifier; one that fails is dropped and the search goes on, as in
  `ruMakeProofFromSteps`.

The variables of an assertion are numbered `0, 1, ...` by its binders, the same numbers
in every assertion; the variables that the prover makes are numbered from 2^16. This is
safe because no variable of an assertion gets into the tree: `expandHyp` replaces each
by an expression over the goal's variables or by a fresh variable.

### MM0 as a deductive system of the paper

- **Language.** A sort is a non-terminal; `term f (a: s1) ... (z: sn): s` is the
  production `s → f s1 ... sn`. Expressions are term trees, so the grammar is trivially
  unambiguous. There is no subtyping between sorts: an MM0 coercion is a term like any
  other.
- **Assertions.** An axiom or theorem is `h1, ..., hk ⊢ c` over its binders. As in
  Metamath, a binder need not occur in the conclusion (`ph` in `ax_mp`); these are the
  variables that `expandHyp` renames to fresh ones.
- **The statement being proved.** Its variables must not be replaced: the paper's
  "non-replaceable" variables. Russell turns them into constants (`ruMakeConstEnv`);
  here they are applications without arguments, in a number range of their own.
- **Definitions** are, in the set.mm translation, axioms (`df_an`): its 1,436 terms
  include no `def`, and its 15.6 million proof commands include no conversion. Both
  acceptance tests of this phase therefore run without `Unfold`. See question 3.

### Where MM0 differs: bound variables

MM0 has two kinds of binders. A regular one, `(ph: wff x)`, stands for any expression of
its sort. A bound one, `{x: setvar}`, stands for a variable only, and comes with
conditions on a substitution `σ` for the binders of an assertion (`safe_subst` in
`mm0.lean`, `argsFault` in our verifier):

1. `σ(x)` is a bound variable of the proof: a bound binder of the theorem being proved,
   or a dummy.
2. For bound `x` and any other binder `v`, the variable `σ(x)` does not occur in `σ(v)` —
   unless `v` is regular and declares the dependency (`v: s ... x ...`). "Occurs"
   includes, for a regular variable of the theorem being proved, the bound variables it
   is declared to depend on.

Both fit the paper's framework, in the two places where the paper already leaves room.

**Condition 1 is subtyping.** The paper lets a variable `v : n` be replaced by `e : m`
when `n → m` is derivable in the grammar, and names the class/set relation of set theory
as the example; the source implements it with `ruSuperRule`. For MM0, give every sort
`s` a second non-terminal `s̄`, "the names of sort `s`", with the production `s → s̄` and
no other production for `s̄`. A bound binder is a variable of type `s̄`; a regular binder
is a variable of type `s`; an argument position of a term that is declared with braces
has type `s̄`. Then condition 1 is the typing rule of substitutions, and nothing in the
algorithm or its proofs changes. In the code this is one bit in the type of a node
(`Ty`), and the test `Ty.fits` where Russell calls `ruSuperRule`; unlike Russell, no
coercion node is inserted, because `s → s̄` has no symbol.

In the set.mm translation this matters: of its 46,520 + 959 binders of sort `setvar`,
959 are regular (`cv (x: setvar): class` takes a regular one), so "sort `setvar`" alone
does not tell whether a variable may be replaced by a regular variable of the theorem.

**Condition 2 is the disjoint variable restriction** that the paper sets aside on its
last page ("the only thing which is necessary to track during traversing of PVT are
these restrictions"). From the binders of an assertion we get its set of pairs
(`disjPairs` in `Db.lean`; 204,328 pairs in set.mm):

    D(A) = { (x, v) : x a bound binder of A, v another binder of A,
                      and not (v regular and x among the declared dependencies of v) }

and the condition on a substitution `θ` is: for each pair, the name `θ(x)` does not occur
in `θ(v)`.

How this relates to the three theorems of the paper. A substitution proof tree now
stands for a proof *under conditions*: the pairs of all its assertion nodes, with its
substitution applied. Write `C(T)` for them.

- *Correctness.* If `η` instantiates the remaining variables of `π(T)` and satisfies
  `η(C(T))`, then `η(π(T))` is a valid MM0 proof. This is the paper's theorem 1 plus the
  observation that MM0 asks nothing else of a proof step.
- *Generality and completeness.* Let `π'` be a valid proof. The paper gives a tree `T`
  congruent to it with `π' = ε(π(T))`. The conditions that `π'` satisfies at its steps
  are exactly `ε(C(T))`. So `C(T)` is satisfiable, and `T` is lost only if the engine
  discards a tree whose conditions are still satisfiable. Hence the rule: **a tree may
  be discarded only when a condition is violated for every instantiation** — the name
  `θ(x)` already occurs in `θ(v)`, as a bound variable of the theorem, as a dependency of
  one of its regular variables, or as the same variable of the tree. A condition that
  could still go either way (because `θ(v)` contains a variable, or `θ(x)` is one) must
  not be decided.

What is built (`judge`, `openConds` in `Proofs.lean`) is this rule with the conditions
carried, as the brief asks ("carried as constraints on the substitution and discharged
consistently"). A condition is judged as one of three things:

- *violated*: the proof is discarded;
- *settled*: nothing can change it any more, and it is forgotten. A bound variable of the
  theorem against an expression without variables; or a name of the tree that no node
  above can replace, which will become a dummy of its own;
- *open*: it stays with the proof (`Proof.prop ... conds`), goes up with it, and is
  judged again under every substitution that the proof is joined with.

So a proof that is doomed stops where it becomes doomed, and a proof at the root
satisfies every condition up to the choice of what is put for the variables that are
left; that choice leaves out what would make an open condition false. "No node above
can replace it" is decided by change 5 below: the variables visible above a node are
those of its expression under the substitution of the proof.

The first version did less, which is what Russell does in effect (change 3 below): it
discarded what was violated for certain and remembered nothing. On the logic fixture
the search for `alrimi` then sent one proof to the verifier to be rejected; now that
proof stops in the tree. On the predicate calculus of set.mm the first version sent 361
proofs to the verifier to be rejected; now none gets there ("The search test").

### Where the code does something else than the source

Each of these is also noted in the file it concerns.

1. **No coercion nodes** (`Subst.lean`, `Unify.lean`, `Index.lean`). Where Russell wraps
   an expression into the rule that lifts it to the type of the variable, the types
   must fit and the expression is taken as it is.
2. **Which of two variables is bound** (`Index.lean`). In `ruDoUnifyIndex`, `unify_var`
   asks `ruSuperRule(var.type, ex_type)`: the two types in the other order than
   `ruAdd2Subst1` has them. With explicit coercion nodes in Russell's expressions the
   case may never arise there. Here a variable is bound to what fits it, and of two
   variables the more general is bound to the more special (a regular variable to a
   name), as `ruUnifyStepVar` does in `exps.flow`.
3. **The disjointness check looks through `outer`, and remembers** (`Proofs.lean`).
   `ruAddProof` calls `ruCheckDisjs(theta, prop.assertion.infer.vars.disjs)`. `theta`
   binds variables of the tree; the pairs are over variables of the assertion, which
   only `outer` binds. So every lookup returns the variable itself, the two sides never
   share a variable, and the check lets everything pass: Russell finds a violated
   restriction only when the finished proof is verified. Here the two binders of a pair
   are looked up through `outer` and then `theta`, and what is still open is carried
   (above). An assertion without premises is checked too when its node is expanded;
   `ruExpandProp` records its proof without looking at the pairs.
4. **`ruMakeFresherSubst`** records, as the variables of the image `v'` of `v`, the set
   `{v}`; here `{v'}`, as for every other entry (`Subst.lean`). In Russell the entry is
   then not updated when `v'` is bound later, and the statement of a step keeps `v'`
   until a step above applies its substitution to the whole subtree.
5. **Substitutions are restricted on the way up** (`Proofs.lean`). In Russell the
   substitution of a proof contains every binding made below it
   (`theta = ruCompose(prop.sub, unif.sub)`, where `unif.sub` joins the full
   substitutions of the children). It grows with the subtree, and every level composes
   it again: replaying a proof of 7,562 steps took 5 s. Here a proof of an expression
   node goes up with the bindings of the variables of that node's expression only. The
   others are of variables made below the node, which occur nowhere else, so the same
   tuples unify with the same result on everything visible. The same proof takes
   0.38 s. One consequence beyond speed: `ruProofSubKey` keeps one proof per
   substitution of an assertion node, and two proofs that agree on what is visible above
   now have the same key although they differ below. Keeping one of them is right when
   either can stand for the other in every proof above: when they also have the same
   open conditions on bound variables. So the open conditions are part of the key
   (question 5).
6. **Proof extraction in one pass** (`makeProofTree`). Russell instantiates a step by
   its own substitution and then applies the substitution of every step above it to the
   whole subtree. After change 5 the substitution of a step no longer contains those
   below it, so the bindings of all steps are collected into one substitution, from the
   root down, and applied once to each expression. A variable can be bound below and
   free above (two variables identified in opposite directions at two levels); the
   binding from below is then redundant under those from above and is left out.
7. **One index with ranks** (`Index.lean`). Russell builds an index per theorem to be
   proved, from the assertions that precede it. Here one index holds all conclusions,
   each with the number of its assertion; a node knows the smallest number below it, and
   a lookup with a limit does not walk the branches that have nothing below the limit.
8. **The trie** is one array of nodes with child lists; a variable is a key together
   with its type, because the binders of different assertions share their numbers but
   not their types; the sets `ends`/`lens` are filled by a pass over the inserted
   expression instead of Russell's recursion.
9. **`ruDoApplySubst`** sets the lengths of applications again from the right, by the
   arity; here from the left with a stack of open applications, a node having no arity.
10. **The root and the premises.** `ruInitProver` expands the root but does not match
    it with the premises, so a goal that is one of the premises (set.mm has `idi`)
    would not be proved. `search` checks this case first.
11. **Restrictions instead of replaceable functions.** Russell's oracle replaces
    `fns.unifyAssertion` and `fns.unifyPremise` of the environment. Here a strategy
    passes, with each node to expand, what its premises may use (`Only`).

12. **A fact is used with fresh variables** (`Forward.lean`). A fact with variables is
    a lemma, and each use of it gets its own copy of them, as each use of an assertion
    does. In `ruApplyForward` the variables of a fact are the same in every use, so one
    fact cannot fill two hypotheses of an assertion in two different instances:
    `ruUnifySubs` then has to make the instances equal.
13. **Facts are told apart up to the names of their variables.** Russell's `seen` has the
    nodes as they are, so a fact derived twice with other fresh variables is two facts.
14. **No `ruJoinAcyclic`.** Facts are derived from the premises and from assertions
    without hypotheses, never from a subgoal, so a join cannot make a proof depend on
    itself. The source says the same of its own check.
15. **Limits inside the forward work.** One application is held to the room that the
    front has left, and the time limit is looked at between two joins of a fact with a
    subgoal. In Russell both are looked at between applications; a fact that unifies
    with thousands of subgoals then runs far past the limit.
16. **`ruUnifySubs` without `ruSplitSubs` for small substitutions**, and
    **`ruUnifySubsProd` not for a product with one large set**. With substitutions
    restricted (change 5) the splitting cost more than it saved; and when only one
    premise has many proofs, walking them is all that either way can do.

### Emission

A proof tree is closed, and becomes a proof body of the `.mmb` format (`Emit.lean`).

- **Closing** (`closings`, `mergeNames` in `Prove.lean`). Variables may be left that
  nothing determined. A name becomes a `Dummy`. A regular variable must be given an
  expression, because MM0 has no dummy that is not a bound variable: a new name if the
  sort has bound variables, a term without arguments declared before the theorem, or a
  variable of the theorem; up to four choices are tried against the verifier. MM0 allows
  55 bound variables in a theorem, and the most general proof has a name of its own
  wherever the known proof used one again; if there would be too many, each leftover
  name is replaced by the first earlier one that no step needs it to differ from.
- **The body**: for each hypothesis of the theorem its expression and `Hyp`; then the
  proof, each step as the proofs of its premises, the expressions for *all* binders of
  the assertion, the conclusion, and `Thm`.
- **Identity.** The format compares expressions by identity, so every expression is
  built once, saved if it is needed again, and referred to afterwards. Subproofs are
  shared by what they prove, as `ruMakeLinearProof` shares the steps with the same
  statement. A step can prove what a step below it proves already (set.mm, theorem
  2019), so a proof counts as made when the step is complete, not when it is first
  asked for.
- The order of all requests is fixed by one function (`plan`) that runs twice: once to
  count, once to write.

`Verify.checkBody` checks a body that is not in the file against the statement of the
theorem, with what is declared before it; `Mmb/Write.lean` writes the file with the new
bodies.

### The replay test

    mm0-whitehead prove replay setmm.mmb -o out.mmb

A proof body gives the tree of the assertions it uses and how the subproofs nest
(`Db.skeleton`); every expression is forgotten. The oracle strategy expands, at each
expression node, only the assertion that the known proof uses there. The engine finds
all substitutions by unification.

| | |
| - | - |
| theorems with a proof | 47,611 |
| reconstructed | 47,611 |
| steps | 3,508,182, the same as in the file |
| tuples that did not unify, proofs rejected by the verifier | 0, 0 |
| proof bodies | 32.4 MB in the file, 32.7 MB reconstructed |
| time | 79 s |

`out.mmb` is accepted by our verifier against `setmm.mm0`, by `mm0-rs`, and by mm0-c.

### The search test

    scripts/search-baseline.sh          # mm0-whitehead prove search, per section

Every theorem of a section is proved from scratch: the engine is given the statement
and the assertions that precede it, and no proof. The strategy is breadth first, all
leaves round by round, with nothing to rank them. The limit is 1 s per theorem. A
section is told by the numbers of its theorems: propositional calculus is what comes
before the term `wal` (theorems 0 to 1532), predicate calculus what comes before
`ax_ext` (1533 to 2824).

| | propositional | predicate |
| - | - | - |
| theorems | 1,520 | 1,262 |
| proved | 805 (53.0%) | 374 (29.6%) |
| stopped at the limit | 715 | 888 |
| proofs rejected by the verifier | 0 | 0 |
| steps of a proof found: median, largest | 2, 4 | 1, 3 |
| proofs of 0, 1, 2, 3, 4 steps | 2, 26, 501, 268, 8 | 3, 300, 57, 14, 0 |
| shorter than in the file / the same / longer | 15 / 594 / 196 | 233 / 134 / 7 |
| time of a successful search: median, 90% | 272 ms, 699 ms | 3 ms, 611 ms |

The files with the proofs found in the place of the original ones are accepted by our
verifier against `setmm.mm0` and by `mm0-rs`.

What the numbers say:

- In one second the tree reaches about 500,000 assertion nodes, which is depth 3 to 4.
  A proof found has at most four steps; whatever needs five is out of reach of an
  unguided search at this budget. This is the baseline that ranking has to beat.
- A proof found can be longer than the one in the file (196 in propositional calculus):
  within a round the first proof that reaches the root is taken, not the shortest.
- In predicate calculus 300 theorems are proved in one step, 233 of them by a shorter
  proof than the file has: they are instances of an assertion that precedes them.
  set.mm proves many statements a second time, from other axioms or by another route
  (`minimp_ax1` is `ax_1` derived from a single axiom, in 3 steps), and a search that may
  use everything before a theorem finds the first one.
- Outside the two sections, a sample of every 250th theorem (179 theorems) has 3 proved,
  each in one step.

More time helps, slowly. A sample of every tenth theorem of the two sections, with a
limit of 10 s or 3,000,000 assertion nodes (the node limit was reached first in 80 of
the 97 searches that were stopped):

| | propositional | predicate |
| - | - | - |
| theorems in the sample | 154 | 127 |
| proved at 1 s | 87 (56%) | 41 (32%) |
| proved at 10 s or 3,000,000 nodes | 122 (79%) | 62 (49%) |
| largest proof found | 4 steps | 3 steps |

Six times the nodes buy one more round of the tree for some theorems, and no proof of
more than four steps.

The forward direction, on the same sample of every tenth theorem, 1 s per theorem
(`prove search --strategy bfs|forward|both --every 10`; the front is limited to 512
facts, Russell's `forward-search-size`):

| | propositional (154) | predicate (127) |
| - | - | - |
| backward, breadth first | 91 (59%) | 43 (34%) |
| forward alone | 28 (18%) | 10 (8%) |
| both in turn | 108 (70%) | 49 (39%) |
| proved by both in turn and not by backward alone | 25 | 8 |
| proved by backward alone and not by both in turn | 8 | 2 |

Both directions in turn prove more in the same time, and find proofs of five steps,
where backward alone stops at four. Forward alone ends early: its front reaches 512
facts in about 50 ms, and then there is nothing left to do. All proofs found are
accepted by the verifier. What the joins cost: a fact is joined with every subgoal it
unifies with, and each join is an `addProof` over the proofs of the sibling; with the
first version of the join a single theorem ran for minutes, which is why the join policy
of `ordered`, the limits inside the forward work and `ruUnifySubsProd` are there
(changes 15 and 16).

Carrying the conditions on bound variables matters here. The first version, which only
discarded what was violated for certain, proved 357 theorems of predicate calculus under
the same limit and sent 361 proofs to the verifier to be rejected; with the conditions
carried, 374 are proved and none is rejected.

Speed: a search makes about 500,000 assertion nodes per second, with 300 to 2,800
assertions to choose from. A profile of a search (callgrind), taken when it made
300,000, had the lookup in the index at 30% and 45% in a list of leaves that was
filtered on every expansion; that list is now cleaned once per round. `addProof` is
small as long as the tree is shallow, which is why `ruUnifySubsProd` could wait.

### Unfolding as an inference step (proposal, nothing built)

Decided (2026-10-01): unfolding a definition is an inference step of its own kind. Its
substitution model is not that of an assertion, but to the layer above it looks like
the application of an assertion.

MM0: `def f (xs) {.ys}: s = B`. An expression with `f(args)` and the same expression with
`B[xs := args, ys := some bound variables]` in its place are *convertible*, and a proof
of one is a proof of the other (the proof commands `Conv`, `Unfold`, `Cong`, `Refl`).
The bound variables given for `ys` must differ from each other and not occur in `args`.

The proposal, in the terms of the tree:

- On a `RuProverExp` with goal `G`, beside the `RuProverProp`s of the assertions, there
  is one for every place `π` where `G` has an application of a defined term: *unfold `f`
  at `π`*. It has one child, `G` with `f(args)` at `π` replaced by the body. Its `outer`
  maps `xs` to `args` and `ys` to fresh names; its `sub` is empty.
- And the converse, *fold `f` at `π`*, where the subexpression of `G` at `π` unifies with
  the body of `f`: the child is `G` with `f(xs)` there, under the unifier, which is the
  `sub` of the node.
- The condition on `ys` is a set of disjoint pairs like `RuDisj`, and goes through the
  same check as those of an assertion.
- "Another substitution model": the unifier comes from going to a place and unifying
  there, not from unifying a conclusion with the whole goal.
- For a strategy it is a leaf like any other: it is expanded, gets proofs from its
  child, and passes them down. In the proof body it becomes `Conv` with a conversion
  that is written mechanically (`Cong` down to `π`, `Unfold` there, `Refl` elsewhere).

How it relates to the paper. For a fixed path `π` through term constructors, "unfold `f`
under `π`" is an ordinary assertion: its conclusion is the path with variables for
everything beside it. So the deductive system is the assertions plus this family, and
the three theorems hold for it as for any set of assertions. The difficulty is that the
family is infinite, and a goal that is a variable, or has one, unifies with infinitely
many of its members (the variable can become any path). The engine cannot expand them
all, so the proposal offers a step only at the places that the goal has. A proof that
unfolds inside something that is still a variable in the tree is then not found by this
step. Question 3 is how you want that handled.

### Questions

Answered on 2026-10-01: forward expansion was to be ported next (done, above);
unfolding is to be an inference step (proposal above); the three places in the source
(question 6) need your investigation and stay as they are documented.

1. **When may a disjoint-variable condition be dropped?** A `RuDisj(x, ph)` of an applied
   assertion, under the substitution of a proof, says: the setvar given for `x` does not
   occur in what is given for `ph`. When the setvar is a fresh variable `x_17` (made by
   `fresher` in `ruExpandHyp`) and is still unbound, the condition is kept with the
   `RuProverProofProp` and checked again in the `ruAddProof` of every ancestor. I drop it
   when `x_17` does not occur in the statement of the parent `RuProverExp` under the
   proof's substitution: then no ancestor can bind it, it stays free up to the root, and
   it becomes a dummy variable of the final proof, different from everything. Is that
   right, or can a variable that is absent from the parent's statement still be bound
   later?
3. **Unfolding inside a variable.** With unfolding as a step at a place of the goal
   (proposal above), a proof that unfolds inside what the tree still has as a variable
   is not found. Is that acceptable for a first version, or do you have a way in mind?
4. **A way to ask for an answer substitution.** The brief wants variables in the goal
   that the prover has to find values for (a `RuProverTask` whose goal has variables that
   `ruConstProverTask` leaves alone). The engine does it: asked for `?q -> ps` from `ph`
   and `ph -> ps`, it answers `?q := ps`. There is no command for it: the commands take
   the theorems of a file. And such a proof is not emitted or verified, because there is
   no theorem in the file that states it. Do you want a command for it in this phase,
   and how should its proof be checked?
5. **Fewer proofs kept per node than in Russell.** `ruAddProof` keeps one
   `RuProverProofProp` per substitution (`ruProofSubKey`). In Russell the substitution
   has every binding of the subtree, so two proofs are the same only if they agree in
   every detail. Here a proof goes up with the bindings of the variables of its node's
   statement only (change 5), so two different subproofs of a premise that give the same
   instance of it lead to one proof of the parent, not two. What can be proved is the
   same; which proof is found can differ. Keep it, or keep all as Russell does?
6. **Three places in the source that look unintended**: `ruCheckDisjs` in `ruAddProof`
   (change 3), the variable set of `ruMakeFresherSubst` (change 4), the order of the
   arguments of `ruSuperRule` in `unify_var` (change 2). For the second, the source
   itself has a note: `ruApplyForward` builds its fresh substitution with `ruAdd2Subst`
   "NOT ruMakeFresherSubst: the latter stores each entry's var-set as the ORIGINAL var
   id, so ruApplySubstVars ... won't chase the fresh placeholder into its binding".
7. **`>` in the type of a `def`.** In `.mm0`, `>` separates the argument types from the
   result type: `term im: wff > wff > wff;` is `term im (_ _: wff): wff;` (`arrow-type`
   in `mm0.md`; not `->`, which is only a notation a file may define). The grammar of
   `mm0.md` allows this for `term`, not for `def`; `examples/hol.mm0` writes five defs
   that way, and `mm0-rs` and mm0-c accept them. Our parser accepts them too. Keep
   that, or follow `mm0.md` and reject `hol.mm0`?
