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
| `Whitehead/Verify/Check.lean` | the statements of a proof file: binders, proof body, what must hold at its end; `checkProofs`, and `checkBody` for a body that is not in the file |
| `Whitehead/Verify/Spec.lean` | a proof file against a specification: `matchSpec`; `specNames`, the specification's names for a file without an index |
| `Whitehead/Mmb/Write.lean` | a proof file with other proof bodies |
| `Whitehead/Prove/*.lean` | the prover: see "The prover", "Modules" |
| `Main.lean` | the command line: `dump`, `join`, `verify`, `bench`, `prove replay`, `prove search`, `prove db`, `prove chains` |
| `tests/Tests/Harness.lean` | a counting test harness (`check`, `checkEq`, `skip`) |
| `tests/Tests/Main.lean` | the test driver: the groups, in order |
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
| `tests/Tests/Prove/Subst.lean`, `Unify.lean`, `Index.lean`, `Prod.lean` | expressions and substitutions; unification, the index and the product unifier, also against the reference on random input |
| `tests/Tests/Prove/Engine.lean` | the engine on the logic fixture: database, replay, search in both directions, conditions on bound variables, the proofs kept, metavariables; the replay of set.mm when the corpus is built |
| `tests/Tests/Prove/Chains.lean` | the chain miner on the logic fixture: counts by length, the most frequent chain, the coverage |
| `tests/Tests/Prove/Defs.lean` | definitions on the defs fixture: values, unfolding steps, conversion rules, the full replay (also in rounds), the replay of `peano.mmb` when the corpus is built |
| `tests/Tests/Mutate/Engine.lean` | mutations of a proof file, from a seed |
| `tests/Tests/Mutate/Main.lean` | `lake exe mutate`: our verdict against that of `mm0-rs` on mutants |
| `tests/Tests/Thorough/Main.lean` | `lake exe thorough`: the thorough layer, the prover over every proof file within a time (see "Testing") |
| `tests/fixtures/mmbasm.py` | a hand assembler for small `.mmb` files, used by the `gen.py` scripts |
| `tests/fixtures/mmb/` | `small.mmb` (from `gen.py`): a valid file with one of everything, its specification `small.mm0` and its expected dump |
| `tests/fixtures/disputed/` | hand-assembled `.mmb` files on which the sources disagree |
| `tests/fixtures/verify/` | hand-assembled `.mmb` files, one per rule of the verifier, and `cases.tsv` with the expected verdicts |
| `tests/fixtures/imports/` | specifications with `import`, for the loader |
| `scripts/build-oracles.sh` | builds `mm0-rs`, `mm0-c` (also as `mm0-c-np`, without its `.mm0` parser) and `mm0-hs` into `.tools/bin` |
| `scripts/build-corpus.sh` | builds the `.mm0`/`.mmb` pairs for acceptance testing into `.tools/corpus` |
| `tests/fixtures/prove/` | `logic.mm1`, a small deductive system with proofs, and `defs.mm1`, a copy of `examples/set.mm1` with definitions; their `.mmb` files compiled by `mm0-rs` (`gen.sh`) |
| `scripts/mutation-campaign.sh` | runs the mutation campaigns of the phase 2 acceptance test |
| `scripts/search-baseline.sh`, `scripts/search-summary.py` | run and summarize the search test of phase 3 |
| `scripts/prove-certified.sh` | the prover, then the verified checker of `theory/` (`lake exe certify`) on the file it wrote |
| `theory/` | a separate package with Mathlib: the verification of the engine (`docs/THEORY.md`) and of the verifier (`docs/VERIFIER-THEORY.md`) |

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
  (`\\`, `\"`, `\n`, `\r`, `\xHH` or `\XHH`); an unknown escape is an error here and a warning there.
- **Arrows in a `def`** (`def all: type > term;`) are used by `examples/hol.mm0`. Neither
  `mm0.md` nor the formal specification has them; `mm0-rs` and mm0-c accept them.
  Decided (2026-10-05): do as `mm0-rs` does. It reads what follows the `:` of a `def`
  with the function that reads it for a `term` (`decl` and `arrows` in `mm1_parser`):
  every type before a `>` is an anonymous regular variable after the named binders, and
  a value may follow or not. This parser does the same.

Where `mm0.md` and the formal specification disagree with each other (the `_` row), the
formal specification is followed.

The grammar accepts some things that are wrong for reasons the primary parser does not
look at, and that the elaborator must check: unknown sorts and terms, a variable declared
twice, dependencies on variables that are not bound, a bound variable given dependencies,
a variable binder after a hypothesis.

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
the main cost of elaboration today: `setmm.mm0` (20 MB) loads and elaborates in 0.89 s,
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
  verifier steps through the bytes of proof bodies and unify streams; it decodes the
  binders into arrays, and the specification match decodes unify streams into trees.
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
`mm0-rs` does. The prover's `.mmb` emission (`Prove/Emit.lean`) builds on it.

`dump` writes line by line through a callback rather than building a string: the dump of
the set.mm translation is 15.6 million lines (390 MB), written in 3.5 s.

## The verifier

`verify spec.mm0 proof.mmb` does two things, in two modules (the second uses only the error type of the first):

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
content: the modifiers of a sort, the binders and return type of a term (sort, bound
flag and dependencies of each), and each formula as a tree, the expression elaborated from the `.mm0` text against the
unify stream of the proof file. A definition may have its value in the proof file only.
In a def's value each dummy of the stream must be a dummy of the `.mm0` of the same sort,
and two dummies of the stream may not be one variable of the `.mm0`, since each `UDummy`
makes a new variable.
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
reads it. The prover reads the `.mmb` file alone; the front end stays as it is.

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
  declares at the same place: modifiers of sorts, binders and return types (sort, bound
  flag, dependencies), and every formula against the tree of its unify stream. The two were produced
  independently (ours by parsing notation; theirs by `mm0-rs` or `mm0-hs`). It runs on
  the fixtures of this repository, on the pairs of the MM0 repository, and on the built
  corpus including the set.mm translation.
- Corpus tests run over a checkout of the MM0 repository, named by `MM0_REPO`, and over
  the built corpus in `.tools/corpus`; without `MM0_REPO` the `.mm0` corpus test is
  skipped and the others are reduced to the built corpus, and that is reported. Every
  `.mm0` file of the MM0 repository must parse and round-trip; every file of
  `tests/mm0_mmu/fail` must be rejected, except the one that is grammatical and wrong
  for a later reason. If `mm0-rs` is available (`.tools/bin/mm0-rs`, or `MM0_RS`), the
  joined form of every file with imports is compared with `mm0-rs join`.
- Reader tests decode the file that `MMB-NOTES.md` section 8 annotates byte by byte and
  compare every decoded field with that listing; then they corrupt it, a byte or a few at
  a time, and check the offset and the message of each rejection. A second file, `small.mmb`, has an
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
  verdict (a fragment of the error message), the verdicts of `mm0-rs` and of mm0-c (its
  build without the `.mm0` parser, `mm0-c-np`), and, where `mm0-rs` differs from us, the
  point of section 9 that explains it. The test checks our verdict always and the other
  two when the tools are built. This is the
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
  on 2,000 lookups among 400 expressions; the product unifier with trying every tuple,
  on 3,000 random products, some of chained substitutions.
- The engine is tested on `tests/fixtures/prove/logic.mmb`: every proof of the file
  replays; breadth-first search finds 15 of its 16 theorems (the test asks for 13), none
  by a longer proof than the file's, and the file with the proofs found is valid; so do
  the forward direction and both in turn; a condition on a bound variable is judged
  violated, settled or open in hand-made cases; which proofs a node keeps, and that no
  application is made twice; a goal with a variable gets its answer, and metavariables
  get values. On `defs.mmb`: the values of the defs, the unfolding steps and the
  conversion rules, search and replay, and the replay over the full expansion with
  other variants and in rounds. When the corpus is built, the theorems of set.mm
  numbered below 6,000 (5,899 proofs) and `peano.mmb` are replayed and the resulting
  files are verified.

### Two layers

`lake test` is the fast layer: fixtures, hand-written cases and samples of the corpus,
in seconds (a few minutes with the corpus built). `lake exe thorough`
(`tests/Tests/Thorough/Main.lean`) is the thorough layer, for the prover, and takes the
time it is given (`--minutes`, 30 by default) on every proof file there is: the corpus,
with the specification beside each file, and with `MM0_REPO` the proof files of the MM0
repository. A file that the verifier rejects (`hello_assembler`, with its `sorry`) is
skipped and said so.

1. The replay test on every file in full. Every proof without a shared conversion must
   be reconstructed, step for step.
2. The search test on samples: every `--every`-th theorem (10) of the first two parts
   of set.mm, backward and in both directions, and of `peano`, 1 s each, one search
   per physical core as `scripts/search-baseline.sh` runs them. No proof found may be
   rejected by the verifier; the fraction proved has a floor well under the baseline
   (30%, 35% and 20%), which only a gross regression would go under, since what a
   second buys depends on the machine.
3. The replay over the full expansion (`prove replay --full --total`), in rounds within
   a share of the time: the files with fewer than 6,000 theorems in full, each within
   an equal share of half the time left (most end in seconds and give the rest back),
   then the larger ones with the stride, smallest first, each with the share of what
   is left that its sample is of the samples left, so that what one gives back goes to
   the larger ones after it — set.mm, the largest, gets the most and runs last. No
   tuple of the known proof may fail to unify and no proof may be rejected; at most 5%
   of the theorems of a file may stop at a limit (the whole of set.mm has 2.9% after
   two hours; every tenth theorem 3.7% after 13 minutes and 2.1% after 25; the
   example files stay under 1%), and each that does is named with its limit.

Every file with new bodies is written to `.tools/thorough` and checked by our verifier,
matched against its specification where there is one, and accepted by `mm0-rs` when it
is built (`.tools/bin`). The stride, the time, the jobs and the memory limit are
options; the three thresholds are constants of the driver, with the measured values
beside them.

### External tools and the acceptance corpus

Neither is under version control; both are rebuilt by scripts.

- `scripts/build-oracles.sh` builds `mm0-rs` (the reference implementation), `mm0-c` (a
  second verifier and the speed yardstick; also `mm0-c-np`, built without its `.mm0`
  parser, which the case test runs) and, with `--with-hs`, `mm0-hs` (needed only to
  translate set.mm) into `.tools/bin`, without writing into the MM0 checkout.
- `scripts/build-corpus.sh` compiles every example that has a specification into
  `.tools/corpus/<name>.mmb` with its joined `<name>.mm0`, translates set.mm (given as
  `SET_MM=/path/to/set.mm`, with `mm0-hs` built) into `setmm.mm0`/`setmm.mmb`, and
  prints what `mm0-rs` and mm0-c say about each pair.

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

### The Russell version ported

The port was read from `russell-flow` at `d3afce64` (2026-08-24); every citation of a
Flow9 file or function in this document and in the code refers to that version unless
a later commit is named. The Russell prover was updated from 2026-10-07 to 2026-10-10:
bugs fixed in the engine and in unification, and its algorithms optimized. Reviewed on
2026-10-11 against the port:

| commit | what | here |
| - | - | - |
| `b3856374` | the per-step `$d` check never fired; a root proof needing more `$d` than declared stopped the search | the same bug was found in the port (change 3) and fixed; such a proof fails the verifier and the search goes on |
| `4f1d5f09` | the matrix unifier lost bindings: `ruUnifySubs` fed triangular substitutions | not in the port: a random test with chained substitutions passes (`tests/Tests/Prove/Prod.lean`) |
| `ab0b99fe` | super-rule arguments swapped in the index | the third source oddity of question 6 (change 2); the port binds the more general variable |
| `47c52bdf` | matrix unifier: columns only for shared variables, one n-ary unification per group | ported |
| `ba2dd6a7` | lazy candidate props | ported (`splitProp`): full replay of theorems 1380–6000, 103 s → 64 s |
| `7657286c` | linear fast path for `ruCompose` | ported: 64 s → 59 s |
| `a733de8a`, `678c472d` | cheaper dedup of proof variants | the key here is different (decided 2026-10-11) and costs one hash per proof |
| `07af2072`, `0410851a` | quadratic merges of new props | not in the port: leaves are pushed, and cleaned once per round |
| `49935cba` | the oracle as a pure node selector | as here (`oracle`, `oracleAll`) |
| `e381104b` | fresh variables in a band of their own | as here (`freshBase`) |
| `3e145b47`, `25c4be54` | budgets per theorem | here: limits of nodes, time, joined proofs, proofs looked at by joins, facts, and a deadline (`Limits`), and the memory of the process (`memoryLevel`) |
| `f1b9317a` | statements of several expressions | not applicable: an MM0 statement is one expression |

### Modules

| Lean module | Flow9 source | Contents |
| ----------- | ------------ | -------- |
| `Prove/Exp.lean` | `ru/src.flow` (`RuExp`), `ru/util/exp.flow` | expressions as flat arrays of nodes in prefix order, each application with the length of its arguments; paths, replacement of a subexpression |
| `Prove/Subst.lean` | `ru/subst.flow` | `RuSubst`: `ruApplySubst`, `ruAdd2Subst`, `ruCompose`, `ruUnsafeCompose`, `ruMatchExp`, `ruMergeSubst`, `ruSplitSubs` |
| `Prove/Unify.lean` | `ru/unify/exps.flow` | `ruUnifyExps`, `ruUnifySubs` |
| `Prove/Index.lean` | `ru/index.flow`, `ru/unify/index.flow` | `RuIndex`, `ruSetIndex`, `ruIndexSubexpr`, `ruUnifyIndex` |
| `Prove/Db.lean` | `ru/prover/core/util.flow` | the assertions and the values of the defs of a proof file as expressions, the conversion rules (`convRules`), the indexes of hypotheses for the forward front, the task with its constants (`ruConstProverTask`), proofs of the file as trees of assertions and conversion steps |
| `Prove/Prod.lean` | `ru/unify/prod.flow`, `ru/unify/indexes.flow` | `ruUnifySubsProd`, `ruUnifyIndexes`: the tuples of substitutions that unify, without trying each |
| `Prove/Tree.lean` | `core/tree.flow` | the nodes of the tree, the proofs on them, `RuProofTree` |
| `Prove/Env.lean` | `core/env.flow` | `RuProverEnv` |
| `Prove/Proofs.lean` | `core/proofs.flow`, `core/tree.flow` | `ruAddProof`, `ruBuildPropProofs`, `ruBuildExpProofs`, `ruMakeProofTree` |
| `Prove/Forward.lean` | `core/forward.flow` | the forward front: `ruSeedForwardFront`, `ruApplyForward`, `ruExpandForwardProved`, `ruReverseJoin` |
| `Prove/Expand.lean` | `core/expand.flow` | `ruExpandHyp` with the unfolding steps (`convRule`, `convCandidates`), the lazy split of a candidate (`splitProp`), `ruExpandProp` with its join with the forward front (`joinCap`); `ruProveProp` of `prove.flow` |
| `Prove/Prove.lean` | `core/prove.flow`, `core/controls.flow`, `tactics/breadth_first.flow`, `tactics/oracle.flow`, `ruRunForwardWave` | the loop with its limits (`overNow`), the strategy interface, the strategies (breadth first, forward, both in turn, replay of a known proof, over the full expansion); closing and accepting a proof |
| `Prove/Emit.lean` | — | a proof tree as the proof body of a `.mmb` file, a conversion step as `Conv` |
| `Prove/Chains.lean` | `commands/find_linear_chains.flow`, `ml/common_subproofs.flow` | phase 4: the chains of steps of the proofs, their counts and coverage (`mineChains`), for `prove chains` |
| `Prove/Replay.lean` | — | the two acceptance tests as commands: `prove replay` (in rounds with `--total`), `prove search`; the jobs (`runJobs`) and the memory watcher |
| `Mmb/Write.lean` | — | a proof file with other proof bodies |

Not ported, each being a layer of its own in the source: proof fragments
(`fragment.flow`), the forward closure (`forward_closure.flow`), the variant-admission
hook, the seed hooks and the ordered wave of the forward front, statistics, Russell's
concurrency (the port has its own: one theorem per thread, `runJobs`), and the tactic
language.

### The engine

- **The proof variant tree.** Expression nodes (`HypNode`: `RuProverRoot`, `RuProverExp`)
  and assertion nodes (`PropNode`: `RuProverProp`) alternate. They are in two arrays and
  refer to each other by number; Russell has mutable vectors inside the nodes and
  pointers both ways. An assertion node carries the assertion and the unifier in two
  parts: `outer`, on the variables of the assertion, and `sub`, on the variables of the
  goal that the unification had to instantiate.
- **Upward pass** (`Expand.lean`). `expandHyp` unifies an expression node with the
  conclusions in the index and makes an assertion node for each result, holding the
  bindings of the walk, those that bind more first. When the node is expanded,
  `splitProp` turns the bindings into the two parts of the unifier and renames the
  variables of the assertion that it left free with fresh ones (Russell's lazy
  candidates); `expandProp` then makes the child expression nodes, the premises under
  the unifier, matches each with the premises of the task, and expands each child at
  once. So the leaves that a strategy chooses among are assertion nodes.
- **Downward pass** (`Proofs.lean`). `addProof`: when a child gets a new proof, the
  product of it with the proofs of the siblings is walked; for each tuple the most
  general unifier of their substitutions (`unifySubs`) is composed with the node's `sub`
  (unified with it instead when the task has metavariables, which a premise can bind at a
  leaf),
  the conditions on bound variables are checked, and the result is a proof of the
  assertion node. One proof is kept per key — what it shows to the nodes above (change
  5). `buildPropProofs` and `buildExpProofs` carry new proofs to the parent, up to the
  root.
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
safe because no variable of an assertion gets into the tree: `splitProp` replaces each
by an expression over the goal's variables or by a fresh variable.

### MM0 as a deductive system of the paper

- **Language.** A sort is a non-terminal; `term f (a: s1) ... (z: sn): s` is the
  production `s → f s1 ... sn`. Expressions are term trees, so the grammar is trivially
  unambiguous. There is no subtyping between sorts: an MM0 coercion is a term like any
  other.
- **Assertions.** An axiom or theorem is `h1, ..., hk ⊢ c` over its binders. As in
  Metamath, a binder need not occur in the conclusion (`ph` in `ax_mp`); these are the
  variables that `splitProp` renames to fresh ones.
- **The statement being proved.** Its variables are free variables: they must not be
  replaced, the paper's "non-replaceable" variables. Russell turns them into constants
  (`ruMakeConstEnv`); here they are applications without arguments, in a number range of
  their own. A variable can be marked as a *metavariable* instead (`Db.task`): it stays
  a variable of the tree, the prover finds a value for it, and the value is reported.
  How the mark is written is a stub (`prove search --meta`, by the number of the
  binder): MM0 has no syntax for it. Only regular binders can be marked, and the proof
  found, which proves an instance of the theorem, is not written or checked.
- **Definitions.** A `def` is unfolded by a step of its own, given by the def and the
  place in the statement ("Unfolding as an inference step" below). In the set.mm
  translation the definitions are axioms (`df_an`): its 1,436 terms include no `def`
  and its 15.6 million proof commands no conversion, so its two acceptance tests do not
  touch this; the files compiled from the examples of the MM0 repository (`peano`,
  `hol`, `mm0`, `x86`) do.

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
those of its expression under the substitution of the proof. That a condition on a
fresh name may be forgotten once the name is not visible above was confirmed on
2026-10-05.

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
   name), as `ruUnifyStepVar` does in `exps.flow`. Of two that fit each other, since
   2026-10-13 the *fresher* is bound (`fresher`, `Exp.lean`): an assertion's variable
   before any of the goal's, then the one with the larger number, so that a
   metavariable is never bound to a variable made later. Russell and the port before
   that took the later one by position, which bound a metavariable to a fresh variable
   at a2i's node of `a2d` with two metavariables; both are most general unifiers, but
   the node-by-node test against the keyed engine (`docs/THEORY.md`, milestone 15)
   needs the two engines to agree on it, and the reference engine's unifier binds the
   larger number. The same test found `Binds.bind` reporting a cycle where the
   variable to bind is already what the target is bound to — a premise with two
   metavariables against the node that has them swapped — which lost the proof;
   `bind` now resolves the target's chain of variables first (`Index.lean`).
3. **The disjointness check looks through `outer`, and remembers** (`Proofs.lean`).
   `ruAddProof` calls `ruCheckDisjs(theta, prop.assertion.infer.vars.disjs)`. `theta`
   binds variables of the tree; the pairs are over variables of the assertion, which
   only `outer` binds. So every lookup returns the variable itself, the two sides never
   share a variable, and the check lets everything pass: Russell finds a violated
   restriction only when the finished proof is verified. Here the two binders of a pair
   are looked up through `outer` and then `theta`, and what is still open is carried
   (above). An assertion without premises is checked too when its node is expanded;
   `ruExpandProp` records its proof without looking at the pairs. A condition is
   settled when its name is a variable that no node above can replace: since
   2026-10-14 the variables a node above can replace are those of the parent's
   expression under `theta` *and of the metavariables' values* under it
   (`visibleVars`), a metavariable's binding going up with every proof; before, a
   name inside a metavariable's value was judged settled and its condition dropped,
   though a node above could identify it with a name of the condition's expression.
   Found by the proof of the keyed engine with conditions (`docs/THEORY.md`,
   milestone 16), not by the tests.
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
   0.38 s. Since 2026-10-13 the bindings of the task's metavariables go up too: a
   premise with a metavariable can bind it at a leaf without its occurring in the
   expressions between the leaf and the root, and without the binding two leaves could
   bind it differently unnoticed (`docs/THEORY.md`, milestone 5).

   **Which proofs are kept** (decided 2026-10-05, refined 2026-10-11). `ruAddProof`
   keeps one proof of an assertion node per substitution (`ruProofSubKey`): of the
   tuples of child proofs that compose to the same `theta`, the first. The source gives
   the reason in a comment ("interchangeable for everything upstream"); the paper does
   not: its generality theorem gives every valid proof a tree of its own shape, and a
   proof that is dropped has none. So on 2026-10-05 `addProof` dropped nothing. On
   2026-10-11 the rule became: one proof per *key* — the substitution restricted to the
   variables of the parent's expression together with the open conditions on bound
   variables (`proofKey`). That is all a proof shows to the nodes above (the parent's
   proof goes up with these bindings only, `restrict`, and the conditions are all that
   is judged later), so two proofs with one key stand for each other in every proof
   above, and the goals proved and the substitutions found at the root are the same
   with one as with both; what is lost is the other subproof below the node. The key is
   coarser than Russell's, which tells apart proofs that differ only in variables made
   below the node, whose number multiplies with every step (`propeqop` of set.mm: a
   million proofs on one node after 14 expansions).

   No proof is made twice either: a tuple of child proofs is joined when the last of
   its members arrives (`addProof` takes the new proof alone for its own node and the
   proofs of the siblings — all of them, or from 64 on those whose key unifies with the
   new proof's, `catchUp`), and at no other time.
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
    would not be proved. `searchCore` (under `search` and `searchWith`) checks this case first, by unification: a goal with
    metavariables is proved by a premise that it unifies with.
11. **Restrictions instead of replaceable functions.** Russell's oracle replaces
    `fns.unifyAssertion` and `fns.unifyPremise` of the environment. Here a strategy
    passes, with each node to expand, what its premises may use (`Only`).

12. **A fact is used with fresh variables** (`Forward.lean`). A fact with variables is
    a lemma, and each use of it gets its own copy of them, as each use of an assertion
    does. In `ruApplyForward` the variables of a fact are the same in every use, so one
    fact cannot fill two hypotheses of an assertion in two different instances:
    `ruUnifySubs` then has to make the instances equal.
13. **Every derivation is a fact, and an application is made once** (`Forward.lean`;
    decided 2026-10-05). Russell keeps the statements of the facts in a set `seen`, and
    drops a statement that is derived again (`ruFwdRegister`); a fact is used with one
    proof ("One proof per matched fact suffices"). That is not proved safe, and for MM0
    it is not safe: two derivations of one statement can leave different conditions on
    bound variables open, and only those of the first would ever be used. So there is no
    `seen`: a statement derived in two ways is two facts, each with its one proof, and
    each is used wherever the statement is.

    Without `seen` the wave of `ruApplyForward` makes the same application — the
    assertion with the same fact for each hypothesis — again for each of its facts
    that is the trigger while the others are in the front. That is the same proof
    twice, not two variants. So the applications that have been made are kept
    (`Forward.applied`), and `addProof` passes over a tuple that is among them. What is
    passed over is, fact for fact, a proof that is there. (A first version made an
    application only when the newest of its facts was the trigger. That needs no
    record, but under the limit of facts it puts an application off to a wave that
    never comes: by itself it took the forward-only sample from 38 proved to 22.)
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
  sort is neither `strict` nor `free` (it may then have a dummy, `closers`), a term without arguments declared before the theorem, or a
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
| time | 77 s on one processor, 8.8 s on 24 (2026-10-12) |

`out.mmb` is accepted by our verifier against `setmm.mm0`, by `mm0-rs`, and by mm0-c.

### The replay over the full expansion

    mm0-whitehead prove replay setmm.mmb --full [--others N|all] --max-tuples T

The test of the engine in its hard regime (after Russell's oracle tactic,
`tactics/oracle.flow`). Every expression node is expanded without restriction, so it
gets all its variants — every assertion that the index finds, every unfolding, every
premise it unifies with — and the strategy (`oracleAll`) clicks those of the known
proof; with `--others` it expands that many other variants of each node on the way, so
that their proofs meet the known one's in the joins of `ruAddProof`. Every proof that
reaches the root is checked by the verifier; the first that passes counts, known or not
(see below). A tuple budget (`--max-tuples`) ends a theorem as a limit when the joins
would go past it.

    mm0-whitehead prove replay setmm.mmb --full --total 7200 [--factor 4]

Proofs differ a lot in what they need: most are replayed within a small budget, some
need more, a few need far more. With `--total S` the replay runs in *rounds*
(`replay` in `Replay.lean`): the first with small limits per theorem (1 s, 100,000
nodes, 10,000 joined proofs, 1,000,000 proofs looked at in joins; `--ms` and the others
set them), every next with `--factor` times the limits of the one before, on the
theorems that stopped at a limit in the round before — until none is left or the S
seconds are out, which also ends the searches under way (`Limits.deadline`). The whole
run has a fixed time and a fixed memory (`--max-mem`), and the budget per theorem is
not chosen in advance but grows as far as the time allows. A theorem's statistics are
those of its last round.

A search says which limit stopped it (`Stop`: time, nodes, tuples, work, memory), and
only a theorem whose limit grows in the next round is tried again. The tuples of a
join are made at once (`unifySubsProd`, `tuplesUpTo`), each with its unifier and its
proofs, about 5 KB; their budget is one of memory, and in rounds it grows only up to a
tenth of the memory limit (`tupleCap`) — the first run of rounds multiplied it without
end, and one join took the process from 32 to 44 GB in 15 s, past every check. A
theorem stopped for memory was stopped by what ran beside it (the largest of those
running gives up first, all of them when memory is very short): it waits, and when
nothing else is left, a round with a quarter as many at once takes the waiting ones,
down to one at once, where memory is the limit and the rounds end. Over the memory
limit, the watcher has every search give up and waits up to 15 s for the memory to
come back before it ends the process.

A proof of an assertion node is kept once per substitution of the parent's variables
with its open conditions (`proofKey`, decided 2026-10-11): two such proofs can replace
each other in every proof above. So the proof found need not be the known one, and the
replay accepts any proof the verifier accepts, and reports how many are not the known
one.

First 6,000 statements of set.mm (2026-10-11), no other variants, budget 300,000
unified tuples per theorem: a proof found for 5,896 of 5,899, 7 of them not the known
one; no proof at the root rejected by the verifier; 3 theorems stopped at the budget
(`propeqop`, its neighbour, and one of 21 steps); 183 s, 1.8 GB. 22 million assertion
nodes were made and 33,336 expanded; the products of proofs had 1.82 billion tuples, of
which all but about 950,000 failed to unify (`ruUnifySubsProd` finds those without
trying each). Merging by key removed 5 proofs only: what multiplies is not duplicates
but proofs with different visible substitutions — in `propeqop`, each of the 6
hypotheses `X e. _V` matches each subgoal `?A e. _V`, and the choices multiply along
the proof. Without a budget that theorem took more than 27 GB.

The whole of set.mm (2026-10-12), no other variants, the default limits (60 s, 2,000,000
assertion nodes, 300,000 joined proofs, 20,000,000 proofs looked at in joins), one job
per processor (24): a proof found for 46,254 of 47,611 theorems, 282 of them not the
known one; no proof at the root rejected by the verifier; 1,357 stopped at a limit;
1 h 57 min, 43.5 hours of processor time, at most 25 GB. 8.2 billion assertion nodes were
made and 2 million expanded. The theorems that stop are those with long proofs: every
subgoal that is a bare variable, as the minor premise of `ax_mp`, unifies with nearly
every conclusion, and a proof of a thousand steps has hundreds of such subgoals.

### Concurrency, memory, speed (2026-10-11)

`prove replay` and `prove search` run one theorem per processor by default (`runJobs`
in `Replay.lean`; `--jobs N`): a worker takes the next theorem when it has finished one,
every theorem has a search state of its own, the database and the index are only read,
and the results come in the order of the file, so the output does not depend on the
number of jobs. Memory is limited to 32 GB by default (`--max-mem`): a watcher reads the
resident size every 250 ms; above 80% the largest running search gives up as at a limit,
above 90% every running one does, and above the limit the process stops (exit code 3)
unless the memory comes back within 15 s of every search giving up.

What made the full replay faster, measured on theorems 1380–6000 of set.mm (one job,
2 s per theorem) and on the first 6,000 (one job per processor):

| change | 1380–6000 | first 6,000, others 2 |
| - | - | - |
| before | 103 s | 15 min and more, without limits |
| Russell's lazy candidates (`ba2dd6a7`) | 64 s | |
| Russell's fast `ruCompose` (`7657286c`) | 59 s | 70 s |
| image variables in an array, lazy instances, a bucket sort of candidates | 49 s | |
| proofs appended to a node in place (they were copied at every join: `nfpo` 88 s → 2.8 s) | | 13 s |
| an index of each child's proofs kept on the node for the joins (`catchUp`) | 26 s | 16 s |
| candidates as shared binding lists, a substitution only when expanded; subexpressions precomputed on the trie nodes | 16.6 s | 13.4 s |
| the product unifier walks only the tuples of children of one term, onto one accumulator | 16.6 s | 12.4 s |

(The 6,000 with no other variants: 9 s → 7.1 s → 6.6 s over the last two rows.) Tried and dropped: a
hash map of the children on the wide nodes of the trie (the node under `=` has 1,340),
which changed nothing measurable — a walk reaches a wide node a few hundred times per
theorem.

Where the time goes now (callgrind, theorems 1600–1800). With no other variants: the
walk of the index of conclusions (`unifyRaw`, a third), making the children of an
expanded node from its candidates (a tenth), reading the database (a quarter, fixed),
and a quarter in allocation and freeing spread over all of it. With two other variants
the picture is different: 196 theorems take 8.1 s, of which two take 6.7 s, and the
rest ~0.25 s each (1612: 286,000 tuples of proofs; 1628, 97 steps: 1.2 million tuples,
300,000 of them unified, stopped at the tuple limit before the known proof is joined,
with one other variant as well). An alternative that is a theorem without hypotheses
proves its node at once under another substitution, and the proofs multiply through
the joins up the path: a node with *k* children of two proofs each has up to 2^k. That
is the size of the search space the tree represents, not a cost per tuple (about 3.5 µs
each, all of `addProof` included); the dedup by key removes those with the same
restriction (176,000 of the 300,000 in 1628) and no other. The walk of the product
unifier (`indexesDown`) once built the whole product of the children of the indexes and
let `indexesStep` reject the tuples whose applications differ; it now builds only the
others, in the same order, and pushes its results onto one accumulator — a few percent
on these theorems.

### The search test

    scripts/search-baseline.sh          # mm0-whitehead prove search, per section

Every theorem of a section is proved from scratch: the engine is given the statement
and the assertions that precede it, and no proof. The strategy is breadth first, all
leaves round by round, with nothing to rank them. The limit is 1 s per theorem, and the
script runs one search per physical core: with a time limit, what a search gets done
depends on what shares its core (24 at once on 12 cores: 682 and 347 proved where 12
at once give 840 and 422). A section is told by the numbers of its theorems: propositional calculus is what comes
before the term `wal` (theorems 0 to 1532), predicate calculus what comes before
`ax_ext` (1533 to 2824).

| | propositional | predicate |
| - | - | - |
| theorems | 1,520 | 1,262 |
| proved | 816 (53.7%) | 377 (29.9%) |
| proved, 2026-10-12, one search per core (12 at once) | 840 (55.3%) | 422 (33.4%) |
| stopped at the limit | 704 | 885 |
| proofs rejected by the verifier | 0 | 0 |
| steps of a proof found: median, largest | 2, 4 | 1, 3 |
| proofs of 0, 1, 2, 3, 4 steps | 2, 26, 509, 270, 9 | 3, 300, 59, 15, 0 |
| shorter than in the file / the same / longer | 15 / 604 / 197 | 233 / 136 / 8 |
| time of a successful search: median, 90% | 258 ms, 680 ms | 3 ms, 630 ms |

The files with the proofs found in the place of the original ones are accepted by our
verifier against `setmm.mm0` and by `mm0-rs`.

The test was run three times, as the rule for which proofs `addProof` keeps changed
(change 5):

| proofs kept | propositional | predicate |
| - | - | - |
| one per restricted substitution (2026-10-01) | 805 | 374 |
| one per whole substitution, as `ruProofSubKey` | 825 | 383 |
| every proof (the table above) | 816 | 377 |

The three differ by less than two in a hundred, in no order: the limit is time, so two
runs of the same code differ as well. Keeping every proof costs nothing that shows at
this depth. With the whole substitution as the key, 133 of the 52,866 proofs that
`addProof` made in this test were dropped; with the key of 2026-10-11, which is
coarser, such proofs are dropped again.

What the numbers say:

- In one second the tree reaches about 500,000 assertion nodes, which is depth 3 to 4.
  A proof found has at most four steps; whatever needs five is out of reach of an
  unguided search at this budget. This is the baseline that ranking has to beat.
- A proof found can be longer than the one in the file (197 in propositional calculus):
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
the 97 searches that were stopped; measured before the change of 2026-10-05 in which
proofs are kept, change 5, and not repeated):

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
| backward, breadth first | 89 (58%) | 41 (32%) |
| forward alone | 21 (14%) | 10 (8%) |
| both in turn | 108 (70%) | 46 (36%) |
| proved by both in turn and not by backward alone | 25 | 7 |
| proved by backward alone and not by both in turn | 6 | 2 |

Both directions in turn prove more in the same time, and find proofs of five steps,
where backward alone stops at four. Forward alone ends early: its front reaches 512
facts in about 50 ms, and then there is nothing left to do. All proofs found are
accepted by the verifier. What the joins cost: a fact is joined with every subgoal it
unifies with, and each join is an `addProof` over the proofs of the sibling; with the
first version of the join a single theorem ran for minutes, which is why the join policy
of `ordered`, the limits inside the forward work and `ruUnifySubsProd` are there
(changes 15 and 16).

These are the numbers with every derivation as a fact (change 13). While a statement
was a fact once, forward alone proved 38 of the 281 where it now proves 31: of the 512
facts of a front, some are now the same statement derived in another way. Both in turn
proved 156 or 157 then and proves 154 now, which is within what two runs differ by. A
larger front is not the way out as the wave stands: with 2,048 facts the search for one
theorem ran for two minutes where its limit is 1 s, because the clock was looked at
between applications only and an application joins every fact that fits with every
other. (Since then an application is capped by the room left in the front, the clock
and the memory are looked at before each application and between joins, and `addProof`
looks at the deadline itself; the case has not been measured again.)

Carrying the conditions on bound variables matters here. The first version, which only
discarded what was violated for certain, proved 357 theorems of predicate calculus under
the same limit and sent 361 proofs to the verifier to be rejected; with the conditions
carried, 374 were proved in the run that followed, and none is rejected.

Speed: a search makes about 500,000 assertion nodes per second, with 300 to 2,800
assertions to choose from. A profile of a search (callgrind), taken when it made
300,000, had the lookup in the index at 30% and 45% in a list of leaves that was
filtered on every expansion; that list is now cleaned once per round. `addProof` is
small as long as the tree is shallow, which is why `ruUnifySubsProd` could wait.

### Unfolding as an inference step

Decided (2026-10-01, 2026-10-05, 2026-10-06): unfolding a definition is an inference
step of its own, to the layer above the application of an assertion; and an expansion
is granular — expanding a `RuProverExp` lists all variants of *one* step that concludes
its statement, one node at a time. An unfolding step is given by two things, the def and
the occurrence it is applied at; the conversion proof of MM0 (`Conv`, `Cong`, `Refl`,
`Unfold`, `Sym`) is not in the tree, which is a search space, but is written at emission
from the place.

MM0: `def f (xs) {.ys}: s = B`. An expression with `f(args)` and the same expression with
`B[xs := args, ys := some bound variables]` in its place are *convertible*, and a proof
of one is a proof of the other. The bound variables given for `ys` must differ from each
other and not occur in `args` (`UDummy` in the verifier).

**What is built** (`Expand.lean`, `convRule`, `convCandidates`). On a `RuProverExp` with
statement `G`, beside the `RuProverProp`s of the assertions there is one for

- every occurrence in `G` of an application of a def `f`: *unfold `f` there*, whose one
  child is `G` with the value in that place;
- every occurrence in `G` of an application whose term heads the value of a def `g`, if
  the value unifies there: *fold `g` there*, whose child is `G` with `g(xs)` in that
  place, under the unifier.

Only defs declared before the theorem; not at a variable of `G`. The step is made as an
assertion over variables of its own — the def's arguments, its dummies, and the
variables of the rest of `G` — whose conclusion is `G` with `f(xs)` (or the value) at
the place and whose premise is `G` with the value (or `f(xs)`) there. So `ruExpandHyp`
finds it by unifying the conclusion with `G`, like any assertion; the arguments are
bound by that, the rest of `G` is renamed back, and for an unfolding the dummies stay
free and become fresh names, under the conditions of `D(A)` that a dummy is apart from
every argument and from the other dummies — the pairs `(y, x)` and `(y, y')` of the
rule, which go through `judge` like every other condition, and which `mergeNames`
respects (`nameConflicts`). A `PropNode` carries the step (`Step.conv`) and the rule;
`ruAddProof`, `ruBuildPropProofs` and the strategies see an assertion node like any
other. `makeProofTree` makes a `ProofTree.conv` with the path of the place, which means
the same in the instantiated statement.

How it relates to the paper: for a fixed context `C` (the path through the term
constructors), "unfold `f` under `C`" is an assertion `C[B] ⊢ C[f(xs)]`, and the
deductive system is the assertions plus this family; the three theorems hold for it.
The family is infinite, and this expansion takes of it, at each node, the members whose
context the statement already has. A member whose context goes through a *variable* of
the statement — the variable can become any context — is not offered: there are
infinitely many of them at every variable.

**Emission** (`Emit.lean`): `Conv` with `Cong` at each application on the path, `Refl`
for the arguments beside it, and at the end `Unfold` with the value pushed first (after
`Sym` for a fold), then `Refl`. `Refl` and `Unfold` need the same node on both sides;
the sharing of expressions gives it, as everything beside the path is asked for by both
statements.

**Replay** (`skeletonWithConvs` in `Db.lean`): a proof body with conversions is read
with its expressions, and each `Conv` becomes a step of the rule `conv_s` whose second
child is the tree of conversion rules (`refl`, `cong`, `unfold`, `fold`) that the
conversion proof stands for — the form described under "Unfolding inside a variable"
below — and the oracle clicks those steps like any other. A `Conv` with no unfolding in
it is dropped. A body that shares a conversion (`ConvCut`, `ConvSave`) is not read.
(An earlier reader turned each `Unfold` into a (def, occurrence) step with the path of
its obligation; it could not replay an unfolding inside what the tree has as a
variable, and was removed with the rules below.)

**Results** (2026-10-06). The fixture `tests/fixtures/prove/defs.mmb`, a copy of
`examples/set.mm1` (CC0) whose `df_*` theorems are proved from the definitions: 24 of
its 26 theorems are proved from scratch (3 s each; `bi1` as
`(ax_mp (syl ax_3 ax_1) (unfold wb@[1,0] con1))`), and all 26 are replayed; both files
are accepted by our verifier and by `mm0-rs`. The corpus files with defs, replayed:

| file | theorems | replayed | with an unfolding where the tree has a variable | with a shared conversion, not read |
| - | - | - | - | - |
| `set` | 26 | 26 | 0 | 0 |
| `hol` | 99 | 78 | 1 | 20 |
| `peano` | 2,700 | 2,444 | 206 | 50 |
| `mm0` | 4,895 | 4,450 | 350 | 95 |
| `x86` | 7,671 | 7,058 | 460 | 153 |

Every output is accepted by our verifier against its specification and by `mm0-rs`.
Searched from scratch, breadth first, 1 s per theorem, a sample of every tenth theorem
of `peano` (270 theorems) has 98 proved (36%), with proofs of up to 7 steps, all
accepted by the verifier and by `mm0-rs`.

Every proof not replayed, without exception, unfolds a def at a place that the tree has
as a variable (checked then by a walk of the tree along the known proof, since removed
with that reader). The typical case is
`notan2` of peano: `~(a /\ b) <-> a -> ~b` by `ax_mp` from `bicom` and `notnot`, where
the conversion is on the minor premise of `ax_mp`, whose statement in the tree is the
variable `?X`. That is the gap of this expansion, and it is 7 to 8% of the proofs of
these files.

**Unfolding inside a variable** (`convRules` in `Db.lean`, decided 2026-10-11). A conversion
inside what the tree has as a variable cannot be a (def, occurrence) step of that node.
So, for a file with defs, MM0's own judgment `a ≡ b` is added as assertions: terms `≡`
and `≡'` per sort (`≡'`: the same judgment with at least one unfolding in its proof), and

    conv_s     b, a ≡' b ⊢ a                       Conv
    refl_s     a ≡ a                               Refl
    cong_t     a_i ≡ b_i ⊢ t(as) ≡ t(bs)           Cong (a bound argument is the same name)
    cong'_t_i  the same, ≡' at argument i and in the conclusion
    unfold_f   B ≡ b ⊢ f(xs) ≡ b,   unfold'_f      Unfold
    fold_f     a ≡ B ⊢ a ≡ f(xs),   fold'_f        Symm, Unfold, Symm

The engine does not change: `ruExpandHyp` finds these by unification like any
assertion, every expansion is one step, and the paper's theorems hold as for any set of
assertions. On `?A -> ch`, `conv_wff` makes the children `?b` and `(?A -> ch) ≡' ?b`;
the latter is expanded by `cong'`, one constructor at a time, as `?A` takes shape. `≡'`
keeps `conv` from proving a goal from itself. The dummies of `unfold_f` and `fold_f` are
bound variables kept apart from the arguments and each other. A rule is usable from the
first theorem after the last term it mentions (`Assertion.rank`, `rankLimit`). A file
without defs, such as set.mm, gets no rules. Emission writes a `conv_s` step as `Conv`
with the conversion proof its rule tree stands for; the replay reader reads a `Conv` as
a `conv_s` step over the rule tree of its conversion.

The (def, occurrence) step stays: it is the direct route where the occurrence is there,
and a proof can be found both ways. Only the differential test against the reference
engine turns it off (`Env.convSteps`), as that engine has the conversion judgment as
assertions only (`docs/THEORY.md`, decision 12).

Results with both (2026-10-11):

| file | theorems | replayed | with a shared conversion, not read |
| - | - | - | - |
| `set` | 26 | 26 | 0 |
| `hol` | 99 | 79 | 20 |
| `peano` | 2,700 | 2,650 | 50 |
| `mm0` | 4,895 | 4,800 | 95 |
| `x86` | 7,671 | 7,518 | 153 |

Every proof that does not share a conversion is reconstructed, and every output is
accepted by our verifier and `mm0-rs`. Search: the fixture has 24 of 26 proved at 3 s,
as before, with about 1.5 times the assertion nodes; the peano sample has 97 of 270 at
1 s (98 without the rules). The test of `Defs.lean` proves `ch` from `ph <-> ps` and
`~((ph -> ps) -> ~(ps -> ph)) -> ch`, which needs the conversion inside `?A`.

### Questions

Answered on 2026-10-01: forward expansion was to be ported next (done, above);
unfolding is to be an inference step (proposal above); the three places in the source
(question 6) need your investigation and stay as they are documented.

Answered on 2026-10-05:

- A disjoint-variable condition on a fresh name may be dropped once the name does not
  occur in the statement of the parent `RuProverExp` under the substitution of the
  proof (was question 1): yes. Nothing changed.
- A variable of a goal is marked as a free variable or as a metavariable (was question
  4); the marking is a stub, because MM0 has no syntax for it. Built: `Db.task` takes
  the numbers of the binders that are metavariables, `prove search --meta` gives them,
  and the values found are reported (`Result.values`). Only a regular binder can be
  marked (`Db.metasFault`). A proof for a task with metavariables proves an instance of
  the theorem; it is not written or checked. The root is now matched with the premises
  by unification, so that `?A` is proved from a premise.
- All variants of a proof are needed: one proof per restricted substitution loses
  completeness (was question 5). First built with the whole substitution as the key of
  `ruAddProof`, as in Russell; replaced the same day by keeping every proof (below).
- `>` in the type of a `def`: as `mm0-rs` does (was question 7). It accepts it, and so
  does this parser ("What the parser accepts").

Answered later on 2026-10-05:

- Unfolding a definition is a separate proof step (question 3, in part): so
  unification is not changed, and (c) of the proposal is out.
- "All variants" means every proof (was question 8). The two places where the source
  keeps one proof of several were written without a proof that this is safe:
  `ruProofSubKey` in `ruAddProof` came with a later refactoring of the source, and
  `ruApplyForward` is new code. Built: `addProof` keeps one proof per key, the
  restriction that is all a proof shows upward (change 5, refined 2026-10-11 with the
  decision that proofs with identical restrictions may be merged); every derivation of
  a statement is a fact of the forward front, and an application is made once (change
  13).

Answered on 2026-10-06:

- An expansion is granular: all variants of one step at one node, and an unfolding
  step is a def and an occurrence; the conversion proof of MM0 is emission. Built:
  "Unfolding as an inference step".

Answered on 2026-10-11: the unfoldings inside a variable are to be reached (was question
3). Built: the conversion rules above.

Answered on 2026-10-12:

- **Three places in the source that look unintended** (was question 6): `ruCheckDisjs`
  in `ruAddProof` (change 3), the variable set of `ruMakeFresherSubst` (change 4), the
  order of the arguments of `ruSuperRule` in `unify_var` (change 2). For the second,
  the source itself has a note: `ruApplyForward` builds its fresh substitution with
  `ruAdd2Subst` "NOT ruMakeFresherSubst: the latter stores each entry's var-set as the
  ORIGINAL var id, so ruApplySubstVars ... won't chase the fresh placeholder into its
  binding". Decided: the port keeps what it does at each of the three, which is what
  MM0 needs. Nothing changed.
- **Limits of the forward front that are not dedup** (was question 9): at most 512
  facts (`forward-search-size`), and a new subgoal is joined with the four facts that
  have the smallest proofs (`fwd_cap` in `ruExpandProp`; facts made later find the
  subgoal themselves). Decided: completeness is needed, so no variant is thrown away;
  a bound on the growth of the tree is acceptable when it is configurable, as the
  bounds of the backward tree are (`maxProps`, `maxMs`), because it can always be
  raised — with the limit raised far enough the algorithm is the complete one. So
  both are limits of that kind: the size of the front was one already
  (`Limits.maxFacts`, `--max-facts`); the join cap was a constant of `Expand.lean` and
  is `Limits.joinCap`, `--join-cap N|all`, set into `Env.joinCap` when a search starts.
  The defaults are Russell's, 512 and 4. Nothing is open.

## Phase 4: the interaction layer

Phase 3 was accepted on 2026-10-13. The first design of phase 4 (2026-10-13, kept below
under "Mining and ranking") listed techniques: chain mining, schemas, macro-actions,
ranking and a dataset. It did not say what they serve. This design, agreed with the
author on 2026-10-16, starts from the use instead. Mining and ranking become parts of
it. Only the miner is built.

### Purpose

- **Two uses:** Whitehead is an interactive prover for humans, and one for AI
  agents, which includes benchmarking. Both follow the same procedure; the front-ends
  differ in how they present it.
- **What the engine is for:** to free the layer above it from metavariables,
  substitutions and unifiers. Above the engine, one reasons about the nodes of the
  proof variant tree and their variants only.
- **What an agent does:** it **chooses variants** and **offers intermediate goals**.
  Tactics do the rest of the expansion. "Clicking on a node" (ARGO talk, slide 7) is a
  metaphor for choosing a variant; the work with substitutions underneath is the
  engine's.

### Choosing variants (backward)

- **A variant:** a variant of a goal node (`RuProverRoot`, `RuProverExp`) is one
  candidate step under it. In Russell that is an assertion node (`RuProverProp`); in
  the port it may also be an unfolding step (def, occurrence). A path through the tree
  is chosen node by node, as the backward tree grows from the goal toward the
  premises.
- **Narrowing by filters:** a goal has thousands of candidates at set.mm scale
  (`tree.flow`: about 1,800 for one goal). The agent does not look at each one. It
  applies a filter and gets back the count and a few samples. Guessing from the
  samples, it tightens the filter, or loosens it when nothing is left, until a few
  remain, and then it chooses among them. Example: 30,000 → 300 → 0 (loosen) → 5 →
  choose 2. The procedure is the same for a human and for an AI.
- **A choice is a focus:** the chosen variants are expanded and the others stay as
  leaves. Nothing is pruned, so a fair tactic can still reach every variant, and
  completeness is untouched.
- **The forward direction (decided 2026-10-16):** the agent chooses several facts of
  the forward trees, at least one of them on the front. The engine makes every
  deduction from them, and the agent filters those and chooses some.
  - The engine's forward API does the work (`forwardTriggers`, `applyForward`), with one
    change to the engine: `applyForward` takes the facts that may fill the hypotheses
    other than the trigger (`fillers`), the forward counterpart of `Only`. Without it,
    every fact that unifies fills them, and the chosen facts restrict nothing.
  - A fact expanded under a restriction stays on the front. The applications that were
    left out are made when it is expanded again without one, and only those
    (`Forward.applied`). Tested: a restricted expansion followed by an unrestricted
    one gives the same facts as an unrestricted one alone.
  - A trigger is a hypothesis that is not a bare variable (`Db.hypIndexes`). A bare
    variable, such as the minor premise of `ax_mp`, unifies with every fact, so it is
    filled from the front. So `ph -> ps` triggers `ax_mp` and `ph` fills it, never the
    other way round.

### Filters

Built on 2026-10-16 (`Prove/Filter.lean`, `Prove/Pattern.lean`).

- **What a filter is:** a predicate over what an agent chooses among. Backward, that is
  the variants of one goal node; forward, the deductions that `deduce` made. Both are
  seen through a `View`: the step, its name, the number of its premises, the new goals
  it makes, and what it proves. The agent tightens or loosens a filter through its
  parameters. A filter reads the tree and never changes it.
- **Atoms:**
  - `name(G)`: the step's name, `*` standing for any characters (the def's name, for
    an unfolding);
  - `scope(a1, ...)`: an assertion among these (Russell's `scoped` whitelist);
  - `kind(assertion | unfold | fold)`;
  - `premises(N)`, `premises(min=, max=)`: the number of premises of the step. That is
    the number of new goals backward; forward, the hypotheses the deduction used;
  - `goal($ pattern $)`: backward, one of the new goals matches the pattern;
  - `result($ pattern $)`: what the step proves matches the pattern. That is the goal
    backward, and the fact deduced forward.
- **Combinators:** `and`, `or`, `not`, and `all` for every variant. A sample is not a
  filter: `Session.select` returns the count and `n` variants drawn by a pseudo-random
  permutation from a seed, so a replay of the session draws the same sample.
- **Patterns, in `.mm0` notation (decided 2026-10-16):**
  - A pattern is a formula of the specification with holes, such as
    `$ _ -> ( _ -> _ ) $`, read by our `.mm0` parser.
  - A hole is `_`. It fits any argument and needs no coercion; it is switched on only
    for patterns (`MathCtx.hole`), so a specification is read exactly as before.
  - The theorem's variables are what they are in its task (`Db.binderImage`).
  - A pattern matches a statement at its top, node for node, the holes aside. Nothing
    is unified: a variable of the statement that is not the theorem's is matched by a
    hole only.
  - The specification and the proof file number terms differently, since the proof file
    also has the local definitions. `Notation.ofSpec` finds the correspondence by the
    walk of `matchSpec`.
- **Later atoms:** a rank from a ranking model (top k), and a mined chain that starts
  with the variant (see "Mining and ranking").

### One DSL for tactics and filters

Built on 2026-10-16 (`Prove/Dsl.lean`, `Prove/Combinators.lean`); `mm0-whitehead dsl`
lists the components.

- **Grammar:** Russell's (`russell-flow/docs/tactics-language.md`), with formulas
  between `$`s:
  - `term ::= name ( '(' arg ( ',' arg )* ')' )?`;
  - `arg ::= name '=' value | value`;
  - `value ::= number | '$' formula '$' | term`.

  Every parameter can be given by position or by name. Errors give the position and say
  what was expected.
- **Two sorts, then four:** a tactic may take a filter; a filter never takes a tactic. A
  filter in a tactic's place, or a tactic in a filter's, is an error that names both
  sorts. Guides and costs came on 2026-10-17 ("Composable tactics").
- **Tactics:**
  - `bfs`, `forward`, `both`, `done`;
  - `filter(f, t)`: `t`, expanding only the variants that pass `f`;
  - `limited(t, size=, depth=)`: Russell's limiter. The size is a number of assertion
    nodes added, and the depth that of the leaves expanded;
  - `seq(t1, t2, ...)`: each in turn;
  - since 2026-10-17: `search`, `follow`, `first`, and `bfs` with parameters
    ("Composable tactics").
- **A restricted tactic** is handed a tree whose leaves are only those that pass, as
  Russell's `focus` does (`Strategy.restrict`). It works as it always does, and the
  leaves left out stay leaves: nothing is pruned. What the restriction says of a node
  is asked once.
- **Time is not a tactic's business:** a strategy's step reads the tree and has no
  clock, so the time is a limit of the run (`Limits.maxMs`).
- **Russell's selectors** (`all`, `frontier`, `leaf(id)`, `assertion(name)`, for `focus`
  and `track`) choose nodes; filters choose the variants of a node. They are not ported.

### Composable tactics (proposed and built 2026-10-17)

The author's request: tactics made of atoms with simple meanings, put together by
combinators in the DSL. `replay` and `rails` were built to measure a concept. Proposed,
answered by the author, and built on 2026-10-17 (`Prove/Cost.lean`, `Prove/Rails.lean`,
`Prove/Dsl.lean`, `tactics/*.tac`).

#### What Russell has

Checked on 2026-10-17 in `russell-flow`.

- **The author's own engine** (2021–2025, `prover/tactics.flow` and `prover/controls.flow`
  at b65b0b9a):
  - a tactic, `RuProverTactic(description, expand, finished)`, chooses the leaves to expand
    and says when it is finished;
  - `RuProverStrategy(initTactic, nextTactic)` puts tactics one after another;
  - the atoms are `ruBreadthFirstTactic`, `ruGiveupTactic`, and `ruLimitTactic`, which
    limits the time and the counts;
  - `ruFollowProofTactic` (`tactics/follow_proof.flow`, 2021) follows one proof tree. It
    maps the proof's steps to the variants of the tree, by assertion, a level at a time;
  - the replay of similar proofs was begun (`strategies/similar_proofs.flow`): an index of
    every step of every proof, under a tactic that does not expand anything yet.
- **Written in 2026 with Claude, so not authoritative:**
  - one type, `RuProverTactic(toString, tag, step, keep_expanding)`, whose step is
    Expand(leaves), ExpandForward, Switch(next) or Done (`core/controls.flow`);
  - the DSL (`docs/tactics-language.md`):
    - atoms: `bfs`, `forward`, `spr`, `linear-guided`, `oracle`, `ml`, `ap`,
      `follow-proof`;
    - combinators: `seq`, `or-else`, `loop`, `limited`, `focus`, `track`, `scoped`;
    - selectors, guides and realizers (`replay(stored)`);
    - derived tactics: compositions with parameters, in `.tac` files.
- **`spr(attempts)`, the subproof replay, is one atom built of three parts**
  (`tactics/subproof_replay.flow`). `ruIterateTactic` runs a driver that:
  1. takes the deepest open leaf;
  2. looks its goal up in the step index, leaving out the theorem's own steps
     (`ruStepsForLeaf`);
  3. follows each fragment found with `ruBoundedFollowProofTactic`.

  The parts are not in the DSL, and `attempts` is the only parameter. `linear-guided` is
  built the same way.
- **Replay and breadth-first search are put together only one after the other.**
  `spr-bfs.tac` is `limited(loop(seq(limited(spr(3), size=…), limited(bfs, …)), N),
  size=…)`. That is our `seq(replay, bfs)`, which loses ("How much it helps").

#### What composes, and what does not

- **One question each round:** which leaves to expand now. Every atom answers it, and
  every combinator combines answers. This is Russell's model, kept.
- **Two ways of combining exist:** in time (`seq`, `loop`, `limited`), and in space
  (`filter`, `focus`), which restricts the leaves.
- **A third is missing: by order.** `rails` wins because the replay and breadth-first
  search share one order, by cost. Neither time nor space can say that, so
  `Strategy.rails` is one strategy that does four things:
  - where subproofs go down;
  - which subproofs;
  - following them;
  - the order of the search.

#### The design

- **Four sorts, each using only those before it:** filter, guide, cost, tactic.
- **Filter:** a predicate over the variants of a node, as before.
- **Guide:** where the proof fragments for a goal come from:
  - `subproofs(count, rank=, min=, source=, open=)`: the index of subproofs;
  - `proof`: the theorem's own proof, as `oracle` follows it (`Prove.lean`): for tests;
  - later: linear chains, and the proofs of intermediate goals.
- **Cost:** the order of the leaves. `depth(L1, L2, ..., penalty=N)`:
  - the number of assertion nodes above a leaf's goal;
  - a node with one of the labels L1, L2, ... costs nothing;
  - an alternative at a goal where such a node hangs costs its full depth;
  - a goal that such a node left open costs N more;
  - `depth` alone is the depth, and `depth(follow)` is the cost of `rails`;
  - later: the ranks of the ranking layer.
- **Tactic atoms, one meaning each:**
  - `bfs(filter=F, size=N, depth=M)`: every leaf, round by round. With parameters, at
    the author's answer, it is still an atom, since it takes no tactic. It means
    `limited(filter(F, bfs), size=N, depth=M)`;
  - `search(cost, filter=, size=, depth=)`: each round, the unexpanded leaves of the
    least cost. `search(depth)` is `bfs` round for round, on a tree without intermediate
    goals, whose leaves cost less and come first;
  - `follow(g, at=open|root, upto=N, ground=, chain=)`: the fragments of guide `g`, put
    down at the goals chosen and followed step by step, and nothing else. It is Russell's
    `follow-proof` over many fragments:
    - `upto=N`: only at goals with at most N assertion nodes above them that `follow` did
      not expand;
    - `ground`: only at goals without metavariables;
    - `chain`: also at the goals that a fragment left open;
  - `forward`, `both` and `done`, as before.
- **Combinators:**
  - in time: `seq`, `loop`, `limited`;
  - in space: `filter`, `focus`;
  - by order: `first(t1, t2, ...)`, which each round runs the first that has something to
    expand. The others wait. `t1` is asked again every round, since what the others do
    may give it something.
- **Labels: atoms share no state, they speak through the tree.**
  - The search loop writes on each assertion node it expands the label of the atom that
    asked for it (`Env.labels`): `search`, `follow` or, in a session, `choose`.
  - `depth(follow)` reads the labels; `follow` reads them for `upto` and `chain`.
  - So `search(depth(choose))` goes on first from what an agent chose.
  - Russell's `tag` does the same, for statistics.
- **Definitions** are named compositions with parameters, as Russell's `.tac` files:
  - one to a file, `tactics/name.tac`: comment lines `--`, its help, then
    `name(p, q=default, ...) = body`;
  - in the body, `@p` stands for what `p` is given. Russell's `$p` is taken: `$` marks
    a formula here;
  - a call of it is its body, with the arguments put in, by name, by position or by
    default. An error in the body is shown at the call;
  - a definition may be a tactic, a filter, a cost or a guide;
  - the directory is `--tactics DIR`, or `tactics` here, or `tactics` in the repository
    the program was built in;
  - an agent may define its own with the MCP tool `define`. They last while the server
    runs, are never written, and cannot redefine the language's.
- **`replay` and `rails` are definitions now** (`tactics/replay.tac`,
  `tactics/rails.tac`):
  - `replay(...) = follow(subproofs(...), at=@at, chain=true)`;
  - `rails(...) = first(follow(subproofs(...), at=open, upto=@upto, ground=@ground),
    search(depth(follow, penalty=@penalty)))`.
- **One change of meaning:** `upto` counts the nodes above a goal without the penalty.
  `Strategy.rails` counted it, so the two differ only where both `upto` and `penalty`
  are more than 0.
- **Completeness is a property of the cost.** `search(c)` is fair when, for every N, only
  finitely many leaves cost N or less.
  - `depth` is fair.
  - `depth(follow)` is fair too: each fragment is finite, and without `chain` no
    fragment goes down at a goal that a fragment left open.
- **Not ported:**
  - `or-else` is `seq` here, since building a tactic costs nothing;
  - `track` is `follow`;
  - `scoped` is `filter(scope(...), t)`;
  - `iterate` is inside `follow`.
- **Mining and ranking** become guides and costs, besides the filter atoms they are now
  (CLAUDE.md, "Phase 4").

#### How it was checked

- **Labels:** the labels change no tree.
- **`search(depth)`** builds `bfs`'s tree on every theorem of the fixture: the same
  nodes, expanded in the same order, and the same proof.
- **`rails` and `replay` as definitions** build the trees of `Strategy.rails` and
  `Strategy.replay`, on every theorem of the fixture, for ten configurations. The two
  strategies left the library; they are kept in the tests as the reference
  (`tests/Tests/Prove/RailsRef.lean`).
- **set.mm:** before the old strategies left, the definitions and the strategies were run
  side by side (`prove search --tactic`, 20,000 assertion nodes a theorem, so that a run
  does not depend on the clock). The output was the same, theorem for theorem: the
  ending, the steps, the nodes made and expanded, the tuples and the work of the joins.
  The verifier rejected no proof.
  - `rails(10, rank=reach, open=0, upto=1)` on every 40th theorem (1,198): 45 proved;
  - the same on every 10th of the propositional and predicate calculus (281): 66 proved;
  - `rails(3)` on every 40th: 24 proved;
  - `replay(3)` on every 40th: 13 proved;
  - `rails(3, rank=size, upto=2, ground=false)` on every 40th: 14 proved.

#### The author's answers (2026-10-17)

1. **BFS with parameters:** filters, scopes and limits, as parameters of the atom.
2. **Labels:** acceptable.
3. **Definitions:** the author was not sure where; Russell's way was taken, a separate
   file for each, parsed by the language.

### Intermediate goals

- **What it is:** an expression S offered by a user, who may be a human, an AI, or an
  ML algorithm such as a lemma generator. What S contains is the engine's business.
- **Its role:** S is a hint that *may* lead to a proof. It may, but need not, be
  deduced from the premises, and it may, but need not, be used in the proof of the
  main goal. It does not, in general, split the search into two smaller ones.
- **Deduced forward from the premises:** S becomes a new fact of the forward frontier.
- **Used in the proof of the main goal:** S becomes a node of the backward frontier,
  to be proved backward or reached by the forward frontier.
- **New:** Russell has no counterpart.

**As built (2026-10-16; `Forward.lean`, `offerHint` in `Expand.lean`, `Session.goal`):**

- **S is a goal node of its own.** It has no parent, is expanded backward like the
  root, and is recorded in the backward front so that a fact can reach it. A session
  without a forward front gets an empty one, with the subgoals already made recorded
  (`Env.withForward`). So S is on the backward frontier from the moment it is offered:
  it is proved backward, by choices or runs in its tree, or reached by a fact.
- **Each proof of S becomes a fact of the forward front** (`takeHints`). A proof is
  taken at S's node, as root proofs are taken at the root. From there S is used as any
  fact is:
  - in the proof of the main goal, through the joins with the goal and the subgoals;
  - forward, as an input of deductions.

  A new subgoal is joined with every fact of an intermediate goal that unifies with it,
  whatever the join cap says, since an agent offered it.
- **Holes:** written in `.mm0` notation, S may have holes. Each hole is a new
  metavariable of the sort of its argument, and the proof of S finds its value
  (`Notation.formula`).
- **A guard against loops** (`HypNode.deps`, `Env.mayJoin`):
  - Each fact records the intermediate goals its proof depends on. A fact is never
    joined into the tree of an intermediate goal that it depends on.
  - Without the guard, the fact of S would prove subgoals of S's own tree that unify
    with S, which gives S new proofs, each a new fact, without end.
  - What the guard leaves out is a proof of S that contains a proof of the same
    statement. The engine without intermediate goals reaches those steps by expanding
    the subgoal, so hints only add proofs.
  - A second intermediate goal may use the first, but not the other way round once the
    second depends on the first.
- **Batch searches are unchanged.** Without intermediate goals the engine does what it
  did: the node-limited comparison on the set.mm sample, before and after, is identical
  for `bfs`, `both` and `forward`.
- **Not built: the use of S before it is proved.** The main goal can follow from S
  while S itself is still open. Seeing that would need proofs with S as an assumption
  at a leaf.
  - A node keeps one proof per key (`proofKey`). A conditional proof with the key of a
    real one would make the real one a duplicate and drop it.
  - So the key would have to carry the assumptions used, which changes the keyed engine
    that `THEORY.md` proves.
  - Open point 6.

### The session

- **The tree persists between requests,** with stable node numbers. Built on
  2026-10-16 (`Prove/Session.lean`): `searchCore` is split into `searchStart` (a goal
  that is a premise, the forward front, the root) and `searchLoop`, which runs a
  strategy on the tree as it is. A search stopped at a limit between two steps resumes
  where it stopped. Breadth-first expands the assertion nodes in the order they were
  made, so a resumed search expands what an uninterrupted one does and finds the same
  proof (`tests/Tests/Prove/Session.lean`).
- **Joins are not cut in a session.** A join that a budget cuts short (`addProof`:
  time, tuples, work or memory) keeps nothing, and the joins after it are skipped
  (`Env.overBudget`). The tree is then missing proofs, and a search resumed on it could
  miss a proof. So a session run checks its time and node limits between steps only,
  and runs every join to its end. A tree with `overBudget` set is not resumed.
- **Operations:**
  - `variants(node, filter)` returns the count and samples;
  - `choose(node, variants)` expands the chosen ones;
  - `deduce(facts)` makes the deductions from the chosen facts (`Session.deduce`, built
    2026-10-16). A session that goes forward seeds its front before the root is
    expanded (`Session.start` with `forward`). A strategy that goes forward is not run
    in a session yet: a wave that a limit stops leaves the facts it had not expanded
    off the front;
  - `goal(S)` offers an intermediate goal (`Session.goal`, `goalText`; built
    2026-10-16);
  - `run(tactic)` runs a tactic within its limits;
  - a view of the tree and of the frontier;
  - `proof()` extracts the proof as `.mmb`, checked by the verifier.
- **Front-ends (decided 2026-10-16):** one binary serves both. The simpler one comes
  first (decided 2026-10-16). That is the MCP mode: a server alone, where the human
  front-end needs a VS Code extension and a webview besides.
  - For humans, an LSP server driven by VS Code: the `.mm0` features, plus custom
    requests for the session operations.
  - For AI, an MCP mode that offers the same operations as tools. It is
    deterministic, reports cost, and logs traces.
  - Both use JSON-RPC 2.0 over stdio, through a small JSON module of our own; Lean
    core's `Lean.Data.Json` is not used, to keep the binary independent of `Lean`.
  - The server prints expressions in `.mm0` notation.
  - The human UI is chosen for its UX, not copied from Russell's tree view.
- **The MCP server, built 2026-10-16** (`Mcp/Server.lean`, `Mcp/Tools.lean`,
  `Json.lean`, `Prove/Show.lean`):
  - **Command:** `mm0-whitehead mcp <file.mm0> <file.mmb> [--log FILE]`. For Claude
    Code: `claude mcp add whitehead -- mm0-whitehead mcp file.mm0 file.mmb`.
  - **Loading:** the server loads the pair once and checks that the proof file proves
    the specification (`matchSpec`). It names the assertions by the specification,
    which is what a file without an index, such as set.mm's, needs. set.mm loads in
    1.9 s.
  - **Transport:** MCP over stdio, one JSON-RPC message per line. The server answers
    `initialize` (versions 2025-06-18, 2025-03-26 and 2024-11-05), `ping`,
    `tools/list` and `tools/call`; a notification needs no answer. Its `instructions`
    tell the agent how to work.
  - **Errors:** an error of a tool, such as a choice that is not a variant, is a result
    with `isError`, and the sessions stay as they were. An error of the protocol is a
    JSON-RPC error.
  - **Tools:** `language`, `find`, `start`, `goals`, `variants`, `choose`, `run`,
    `goal`, `facts`, `deduce`, `proof` and `close`. Results are JSON objects.
    - Each result that changes the tree reports what it cost: `ms` and `nodes`.
    - A sample is drawn from a seed, and a run limited by `nodes` is deterministic.
    - With `--log`, every message in and out is written: the trace.
  - **Statements in notation:** they are printed in the notation of the specification
    (`Printer`, which inverts the tables of the `.mm0` parser), and read in it.
    - A variable the engine made is printed `?` and a number. A variable of a variant's
      rule that its unifier leaves free is `?` and the binder's name.
    - Tested: all 170,109 statements of the corpus' specifications print and read back
      to the same expression.
  - **Proofs:** `proof` lists the proof as numbered steps, each with the steps it uses
    and its statement, checked by the verifier.
  - **The first pilot, 2026-10-16:** a Claude subagent worked three set.mm theorems
    through the bridge, ones that breadth-first does not prove in 1 s, with a budget of
    about 40 calls each.
    - **Results:** all three proved, and the verifier accepted each proof:
      - `jaob` in 15 calls;
      - `pm5_32` in 25 calls, with two intermediate goals, both proved and then used;
      - `baroco` in 10 calls.
    - **The agent's own caveat:** it chose nearly every step from its memory of
      set.mm's proofs. The filters let it look up steps it already had in mind; they
      did not let it find steps it did not know. The one structural filter it relied
      on, `goal($ wal _ _ $)`, took 717 variants to 1.
    - **Fixed after it:**
      - an argument a tool does not take is an error that names those it takes;
      - each variant shows what it proves, the goal under its unifier, so a closing
        step shows what it puts for the goal's variables;
      - a goal node shows its number of proofs and, if it has variables, the instances
        proved (`proved_as`), in place of a `proved` that meant "some instance";
      - `run` takes a `node` to work in its subtree (and the language has
        `focus(N, t)`), and reports the goals it closed and the open goals before and
        after;
      - `variants` has a compact mode of one line per variant;
      - the filters `hyp` (a new goal that a premise proves) and `bare` (a new goal
        that is a bare variable);
      - `goals` no longer lists an open intermediate goal twice;
      - the language says that the depth of `limited` counts from the root.
    - **Not done, open point 7:** carrying a closed sibling's bindings to the open
      siblings. In the tree, siblings are independent until their proofs are joined at
      their parent. So what is consistent shows only at the parent, among its joined
      proofs, which the agent sees as `proved_as` there.
  - **The second pilot, 2026-10-16, anonymous:** a Claude subagent worked four set.mm
    theorems with the assertions known only by number: `jaob` again, and `pm5_17`,
    `biadanid` and `_3ianor`.
    - **Results:** all four proved, and the verifier accepted each proof:
      - `jaob` in 13 calls, two of its leaves closed by `run`;
      - `pm5_17` in 24 calls, with intermediate goals and one subtree by `run`;
      - `biadanid` in 25 calls, by hand;
      - `_3ianor` in 23 calls, by hand.
    - **How the agent chose:** by recognizing familiar rules in their statements, which
      is still prior knowledge of set.mm, but not of names. It also came to know a few
      numbers by the third theorem.
    - **What made the decisions:**
      - shape filters on the new goals (`goal($ ... _ ... $)`), which usually took
        hundreds of variants to 1–4;
      - `premises(0)`, for the steps without premises;
      - intermediate goals in place of choosing middle terms;
      - the `used` order helped it find its way, but was not what decided.
    - **Fixed after it:**
      - a new goal without metavariables is closed at once by its variants without
        premises (`Session.closeGround`; `close` in `choose` and `goal`, on by default),
        since such a variant proves the goal itself and is not a decision;
      - the filters `proves($ p $)`, on what the step proves, `fits($ p $)`, where a
        metavariable of a new goal matches anything, and `ground`;
      - `hyp` no longer counts a bare-variable goal, which every premise fits;
      - `run`'s `nodes` is what the run may add, not the size of the whole tree;
      - a tool that changes a session takes it out of the server's state while it works
        (`takeOpen`), so the tree is held once and changed in place;
      - each operation's checks are split from its work (`Session.chooseError?` and the
        others), so that an error leaves the session as it was.
    - **Times:** a choice on a tree of 1.1M nodes takes about 15 ms. The 450–650 ms the
      agent saw on a 2M-node tree were the expansions of new goals such as
      `wb ?a ?b`, which unify with thousands of assertions.
    - **Not done:** a tactic that tries short chains of facts without premises. On
      `pm5_17`, breadth-first missed a two-step chain within 3 s.
  - **Anonymous mode** (`mcp ... --anonymous`): every assertion is shown, filtered and
    listed as `A` and its number, except that `start` takes the theorem's real name. An
    agent then chooses by the statements, the filters and the ranks, and cannot look a
    step up by its name. It is for measuring what the tools give when memory cannot.
  - **A bridge for a shell** (`scripts/mcp-bridge.py`): it keeps one server up behind a
    port of 127.0.0.1, and each `call <tool> '<json>'` prints one result. It serves an
    agent that has a shell but no MCP client, and trying the server by hand.
- **The human UI, a first variant (decided 2026-10-16): a goal panel.** It is a webview
  beside the editor that shows one goal node at a time:
  - the path from the root, which is also the way back;
  - the goal in notation;
  - a filter box, with the count and samples of what is left, where the variants are
    chosen;
  - the goals that the chosen variants make, where a click moves the panel;
  - the open goals and the proofs found;
  - a field for an intermediate goal.

  A tree view does not fit: a node may have thousands of variants, goal and step
  levels alternate, and a label holds one line. The author doubts that one goal at a
  time is the best way to move about in a huge tree (open point 4).
- **A session file (proposed, not decided):** each action (`choose`, `goal`, `run`) is
  recorded as a line of the DSL. Replaying the file rebuilds the tree, since the search
  is deterministic, and editing a line is the undo. The traces of an AI over MCP would
  take the same form.

### Measurement

- **Filter quality on set.mm:** the oracle (`Prove.oracle`) knows which variant the
  stored proof uses at each node. For a filter, measure how many variants it leaves,
  and whether the proof's variant is among them. That needs someone who writes the
  filters, an agent, so it comes with the front-ends.
- **The baseline, built 2026-10-16 (`prove variants`, `Prove/Measure.lean`):** how many
  variants a filter has to narrow. A known proof is replayed over the full expansion
  with no other variants, so every goal node on its path is expanded against the whole
  database, and each node where a step is chosen is counted. On set.mm, every 20th
  theorem (2,391 theorems, 84,703 nodes, 10 s each, 148 stopped at the limit with
  their nodes up to there counted):
  - per node: mean 3,394 variants, median 988, 90th percentile 8,967, 99th 33,275,
    largest 48,940;
  - by size: 1.6% of nodes have 11–100, 48.6% have 101–1,000, 41.5% have
    1,001–10,000, and 8.2% have more than 10,000.

  On the propositional and predicate calculus parts, every 10th theorem, the median
  is 203 and the largest 2,760.
- **What a description of the next goals narrows, built 2026-10-16** (`prove variants
  --shapes`, `nodeCounts`, `Exp.shape`):
  - **The filter:** at each node on a known proof's path, the filter that describes the
    known proof's variant without naming it. It gives the number of premises, and the
    shape of each new goal to depth `d`: its terms and the theorem's variables down to
    `d`, and a hole below that and for every variable of the tree. This is what an agent
    could say if it knew what the next goals look like.
  - **A check:** the known proof's variant passes its description at every node.
  - **On set.mm, every 40th theorem (1,198 theorems, 42,582 nodes):**

    | | median left | 90th percentile | 5 or fewer left |
    |---|---|---|---|
    | all variants | 983 | 8,958 | 0% |
    | described to depth 1 | 114 | 1,064 | 9.2% |
    | described to depth 2 | 32 | 802 | 25.8% |
    | described to depth 3 | 16 | 725 | 39.5% |

    On the propositional and predicate calculus parts, at depth 3, the median is 3 and
    57.5% of nodes have 5 or fewer left.
  - **The tail that stays wide:** 1.5% of nodes keep more than 10,000 variants at every
    depth. In a sample of every 400th theorem (3,912 nodes), 375 nodes keep more than
    1,000 at depth 3:
    - 330 of them are steps without premises, for which a description says nothing.
      The goals they close are often bare variables, which nearly every assertion fits;
    - 14 have new goals that are all variables;
    - 31 are other cases.

    There an agent has to name the assertion (`name`, `scope`), or a ranking has to help:
    the rank atom of "Mining and ranking".
- **The first rank, built 2026-10-16** (`Prove/Uses.lean`; the atom `used(N)`; `order:
  used` in the `variants` tool):
  - **The count:** how many proofs of the theorems before the one being proved use the
    assertion. Each proof counts once, and only earlier proofs count, so it is out of
    sample.
  - **Proofs, not uses:** counting proofs is one answer to question 5 of 2026-10-13,
    which is still open. Counting uses would let a subproof used thousands of times in
    a few proofs (`renegcli`) count thousands of times.
  - **Ordering:** `Session.select` with `byUses` gives the variants that pass a filter,
    most used first.
  - **Where the known proof's variant is in that order,** on set.mm, every 40th theorem
    (42,213 nodes; `prove variants --shapes`):

    | among | first | in the first 5 | in the first 10 |
    |---|---|---|---|
    | all variants | 7.9% | 18.5% | 24.6% |
    | those described to depth 1 | 28.1% | 49.8% | 60.5% |
    | those described to depth 2 | 44.8% | 69.8% | 76.8% |
    | those described to depth 3 | 57.0% | 77.0% | 82.2% |
    | steps without premises (14,516 nodes), described | 29.8% | 49.8% | 57.0% |

  - **What this means:** a description of the next goals to depth 3, with the most used
    first, puts the known variant among 5 shown at 77% of nodes. Steps without premises
    are a third of the nodes, and there the order alone does half of that.

### Open

1. How variants are chosen in the forward direction: decided 2026-10-16, see
   "Choosing variants".
2. Which front-end comes first: decided 2026-10-16, the simpler one, MCP.
3. The questions of 2026-10-13: answered 2026-10-17 ("Proof rails"), but for question
   3, which is asked again.
4. How a human moves about in a huge tree. The goal panel is a first variant only.
5. Whether a session is recorded as a file of DSL lines.
6. Whether an intermediate goal should be usable before it is proved: whether the
   agent should see that the main goal follows from S while S is still open
   ("Intermediate goals", "Not built").
7. Whether a choice at one sibling should narrow the variants shown at the others, by
   the bindings of the proofs joined at their parent ("The first pilot").
8. The composable tactics: answered and built 2026-10-17 ("Composable tactics").

### Order of building (a proposal)

1. A resumable search and the session operations as a Lean API, tested on the fixtures.
2. The first filter atoms and combinators, and a `Strategy` that takes a filter: done
   2026-10-16.
3. The DSL for both sorts: done 2026-10-16.
4. Intermediate goals in the engine: done 2026-10-16.
5. The front-ends: the MCP server done 2026-10-16; the human one to come.
6. Filter quality measured on set.mm: what a description of the next goals narrows,
   done 2026-10-16; an agent's own filters, through the MCP server, to come.

### Proof rails (the author's answers of 2026-10-17)

The questions of 2026-10-13, answered by the author:

1. **A linear subproof** is a chain in the proof tree of an existing theorem, from a
   premise up to the node it proves, with the other hypotheses open. It is a linear
   subgraph of a valid proof, and it may start at any node of that proof, not only at
   its root.
2. **Positions are part of a chain,** so that it can be represented as a rule. But chains
   are not to be made into theorems of their own (derived rules): there are too many of
   them. Instead they are **guiding rails**. One rail, or several, is put down at the
   current goal, so that it reaches the premises in one step. The open nodes along the
   rails are then built up into a proof of the goal.
3. Asked again in simpler words, below.
4. Answered: what the first design called a macro-action was a derived rule, a theorem
   made from a chain. Answer 2 drops it.
5. **A subproof used several times in one proof counts once; one used in several proofs
   counts once in each.** This is how `Uses.lean` already counts.
6. **The Russell files** (`subproof_replay`, `linear_guided`, `lgg`, `ml/`) are
   experiments in using subproof replay in the search.
   - Replaying a whole subproof, rather than a linear one, generalizes the idea. Extra
     variants do no harm, so the fragments of any reachable proof are replayed at the
     current goal, in the hope that some part of them is in the final proof.
   - The fragments may be taken from any node of a proof. That needs an index of all
     steps of all proofs, which is huge but may pay off.
   - The difficulties: (a) telling reachable fragments from the others; (b) keeping
     their number under control.

**The idea, in the author's words:** use the fragments of existing proofs to reach from
the current goal to the premises (one of them, several, or all, which are variants) in a
single step; then build up the tree, in the hope that some of these paths are parts of
the true proof.

**The design that follows (proposed 2026-10-17; built, see "The replay" below):**

- **The index of steps** (Russell's `ruBuildStepIndex`): every step of every proof of
  the file, by its statement. A step's variables are those of its theorem, and in a
  replay they are metavariables. As in Russell, a statement that is a bare variable is
  left out, since every goal fits it.
- **A rail** at goal node G is a step of the index whose statement unifies with G. With
  the subproof below it, it is a whole rail. With one path of it, from the step down to
  a leaf that is a hypothesis of its theorem, the other branches left open, it is a
  linear rail.
- **What a rail reaches:** the leaves of the rail that are hypotheses of its own theorem
  become goals here. Some may unify with the premises of the current task (or with
  facts): that is what the rail reaches. It may reach one premise, several, all, or
  none. A filter or a rank says which reach enough.
- **Putting a rail down** expands, in the tree, the variants that the rail's steps name,
  one step after another along it: a tactic of the layer above the engine (Russell's
  `follow-proof` and `track`). Each expansion is an ordinary step. Nothing is added to
  the database, and the variants that the rail does not take stay leaves. The open
  nodes along the rail are then built up by choices, tactics and further rails.
- **(a) Reachable:** a fragment is reachable at a theorem if every assertion it uses
  comes before that theorem. The index keeps, for each step, the last assertion its
  subproof uses. By default only fragments of earlier theorems are used, which are
  always reachable and keep the measurement out of sample. A reachable fragment of a
  later theorem is a configurable option.
- **(b) How many:** the rails at a goal are counted, filtered and sampled like variants
  (by their source, length, what they reach, and how often the fragment occurs), and a
  replay tactic takes a configurable number of them.
- **For the agent:** a `rails` tool at a goal node, with a count and a sample, and a
  tactic to put a chosen rail down.
- **Measured first:** on set.mm, at the nodes of known proofs, how often a rail from an
  earlier theorem reaches the premises, and how often a rail lies along the known proof.

**Is it feasible to cover every distinct subproof by a lemma?** The author's question of
2026-10-17. Measured the same day (`prove subproofs`, `Prove/Subproofs.lean`).

- **What counts as a subproof decides it.**
  - The subproof below a node (everything down to the theorem's hypotheses) is
    feasible.
  - Any connected piece of a proof, cut anywhere, is not: each branch can be kept or
    cut off into a hypothesis, so the pieces grow exponentially with the size of the
    proof.
  - Bounded pieces are feasible: chains of up to 6 steps are 190,000 to 350,000
    distinct ones per length (the chains report of 2026-10-13).
- **The subproofs below a node, hash-consed across set.mm:**
  - **Count:** 47,611 proofs with 3,508,182 steps (counting a shared subproof each time
    it is used) have 664,589 distinct subproofs. By size:

    | steps | distinct subproofs |
    |---|---|
    | 1 | 28,876 |
    | 2–5 | 202,566 |
    | 6–20 | 247,718 |
    | 21–100 | 138,358 |
    | 101–1,000 | 43,253 |
    | more | 3,818 |

  - **The lemmas:** each subproof's most general lemma is made from its children's in
    one unification each. All 664,589 are made, in 11 s for the whole file. 158 have a
    bare variable for a conclusion. There are 615,612 distinct statements.
  - **Coverage:** the share of steps that lie inside a subproof which an earlier
    theorem's proof already has, and which one lemma step would therefore take:
    - 43.2% with each subproof counted once per proof (the author's rule, answer 5);
    - 63.0% counting every use;
    - 22.1% of the nodes of 2 steps or more are such a subproof;
    - 670 proofs (1.4%) are, whole, a subproof of an earlier proof.
  - **Recurring subproofs:** 78,877 distinct subproofs occur in two proofs or more
    (1.6 times the assertions), and 7,910 in ten or more. Those that two earlier proofs
    have cover 36.5% of the steps, each subproof once per proof (56.0% counting every
    use).
  - **The cost in variants,** at the 48,208 goal nodes of the known proofs of every
    40th theorem, each lemma usable only after the proof where it is known:

    | | median | 90th percentile | 99th percentile |
    |---|---|---|---|
    | assertions alone | 983 | 8,963 | 32,657 |
    | with all lemmas of earlier proofs | 5,691 | 94,714 | 484,128 |
    | with lemmas that 2 earlier proofs have | 1,698 | 18,225 | 83,368 |

- **What this means:**
  - A lemma for every subproof below a node is cheap to make. But it multiplies the
    variants by about 6 at the median and 10 at the 90th percentile.
  - The lemmas of recurring subproofs keep most of the coverage (36.5% of the steps,
    against 43.2%) at about 1.7 to 2.5 times the variants.
  - Either way, the filters and ranks are what an agent would choose among them with.
    The occurrences of a subproof are a natural rank.

**The replay, built 2026-10-17** (`Prove/Rails.lean`; the author chose the implicit
replay over lemmas: a pointer to a proof node, replayed, uses every connected piece of
its subproof, since each node it makes meets the premises, the facts and its other
variants):

- **The index:** one entry for each of the 664,589 distinct subproofs below a node,
  keyed by the conclusion of its most general lemma, without the 158 bare ones. A
  theorem finds only those of the proofs before it.
- **`replay(...)`:** puts subproofs down at goals and follows each step by step, by
  position (Russell's `spr` and `follow-proof`). Every step is an ordinary expansion; a
  branch that does not fit ends.
- **`rails(...)`:** replay and breadth-first together, by cost.
  - A replayed step costs nothing, and a searched one costs 1.
  - The alternatives at a goal on a rail cost their depth, as in breadth-first.
  - A goal a rail leaves open costs `penalty` more than the goal the rail went down at.
  - Rails go down at goals of cost `upto` or less (ground ones only, unless
    `ground=false`), never at goals a replay opened.
  - Without rails it is breadth-first round for round (tested on every fixture
    theorem). Every leaf is reached in its turn.
- **Configurable** (the author asked for it):
  - `count`, how many rails per goal;
  - `rank`: occurrences in earlier proofs, size, small, or reach (the fewest
    hypotheses left open first);
  - `min`, the fewest steps;
  - `source`: earlier, or recurring (in two earlier proofs);
  - `open`, the most hypotheses a rail may leave open;
  - `upto`, `ground`, `penalty`.

  `loop(t, N)` repeats a tactic, and the MCP tools are `rails` and `replay`.
- **Reach:** the author's idea, from the goal to the premises in one step. Put down at
  the goal, a subproof's lemma leaves open the hypotheses that no premise of the theorem
  fits. A subproof with none open proves the goal outright.

**How much it helps** (2026-10-17). The test is `prove search --tactic` on set.mm, 12
searches at once, against `rails(0)`, which is breadth-first itself. Every proof found
was checked by the verifier, and none of the 52 runs had a rejected proof. The
subproofs are those of earlier proofs only, so the measure is out of sample.

- **The best configuration** is `rails(10, rank=reach, open=0, upto=1)`: at the root and
  at the goals of the first round, the 10 subproofs that leave no hypothesis open.

  | sample | per theorem | breadth-first | rails | proved that breadth-first misses | lost |
  |---|---|---|---|---|---|
  | all of set.mm, every 40th (1,198) | 1 s | 67 | **103** (+54%) | 41 | 5 |
  | | 5 s | 92 | **122** (+33%) | 38 | 8 |
  | propositional and predicate calculus, every 10th (281) | 1 s | 139 | **160** (+15%) | 33 | 12 |
  | | 5 s | 173 | 173 | 16 | 16 |

  The new proofs run from 2 to 37 steps. `upto=2` gives the same as `upto=1`, and 30
  rails per goal the same as 10.
- **Rails ranked by occurrences, without reach, lose.** With `rails(3)`, 70 of the
  propositional and predicate calculus sample are proved against 139 at 1 s, and 103
  against 173 at 5 s. A penalty narrows the loss (`rails(1, penalty=2)`: 169 against 173
  at 5 s) but does not turn it.
  - The cause: each rail's open goals start their own breadth-first search, and most
    rails are not part of the proof.
  - Measured (`prove rails`): of the first 3 rails at a theorem's goal, by occurrences,
    the best agrees with the known proof in its first step for 12.8% of the propositional
    and predicate theorems, in half its steps for 5.3%, and in all for 0.7%.
  - Ranked by reach, the half-the-steps share is 8.5% (on all of set.mm, 2.5% becomes
    4.5%, and the whole proof 0.2% becomes 1.6%).
- **Combinations that put breadth-first first,** such as `seq(limited(rails(0),
  size=100000), rails(3))`, end about even: 174 against 173 at 5 s.
- **What this means:** a rail pays when it closes the goal, and costs when it opens
  goals that are not part of the proof. Rails that leave nothing open, found by reach,
  are where the gain is. Ranks better than occurrences are what the open rails would
  need: phase 4's ranking layer.

**Ranks for the rails** (2026-10-17, after the composable tactics). The rails that leave
goals open lost because the first few at a goal were rarely the right ones. Better ranks
were looked for offline, then tried in search.

- **The data:** `prove rails --dump` writes, for the goal of each sampled theorem, every
  subproof of earlier proofs that fits it: its size, occurrences, open hypotheses, how
  long ago it was last used, how many nodes of its conclusion are not variables, the uses
  of its top assertion, and how far it agrees with the known proof. Every 10th theorem of
  set.mm gave 1,743,110 rows.
- **Offline,** on the second half of the theorems (out of sample), among the rails that
  leave a goal open, the best of the first 3:

  | rank | the known proof's first step | half its steps |
  |---|---|---|
  | occurrences (as before) | 8.8% | 1.2% |
  | reach | 7.9% | 1.4% |
  | specific: the most nodes of the conclusion that are not variables | 19.1% | 3.4% |
  | recent: in the latest proof before the theorem | 12.4% | 2.5% |
  | a linear model per theorem, learned on the first half | 19.9% | 3.4% |

  The learned model is no better than `specific`, so the two simple ranks went in:
  `rank=specific` and `rank=recent`. On the propositional and predicate calculus,
  every rail counted, `recent` is best: 24.1% and 14.9%, against 12.8% and 5.3% by
  occurrences.
- **In search,** at 1 s a theorem (`--every 40` on all of set.mm, `--to 2825 --every 10` on
  the calculus):

  | tactic | set.mm (1,198) | calculus (281) |
  |---|---|---|
  | `bfs` | 66 | 134 |
  | `rails(10, rank=reach, open=0, upto=1)`, the best before | 102 | 159 |
  | `rails(3, rank=recent)`: open rails alone | 69 | 120 |
  | `rails(3, rank=specific)` | 78 | 115 |
  | **`guided`**: the closing rails, and 1 open rail by `recent` at the root | **110** | **173** |
  | the same with 3 open rails | 105 | 170 |
  | the same with 1 by `specific` | 107 | 170 |

  Penalties of 1 and 3, 2 open rails, or open rails also in the first round, are within
  the noise (106 to 110, 170 to 173). Open rails by occurrences alone proved 54 and 70.
- **At 5 s:** `bfs` 91 and 170, the best before 122 and 170, **`guided` 127 and 188**.
  Against `bfs`, `guided` proves 40 theorems more and loses 4 on set.mm, and 22 more and
  4 lost on the calculus; its new proofs have up to 104 steps. No proof was rejected by
  the verifier in the 32 runs.
- **`guided` is a definition** (`tactics/guided.tac`), made of the atoms only:
  `first(follow(subproofs(10, rank=reach, open=0), at=open, upto=1, ground=true),
  follow(subproofs(1, rank=recent), at=root), search(depth(follow, penalty=2)))`.
- **The variants of a node, by recency** (`prove variants`, every 40th theorem): the
  known proof's variant is first at 10.4% of the nodes by recency, against 8.2% by uses,
  and in the first 10 at 36.7%, against 25.6%. As a cost, `depth(by=recent, width=W)`
  (a step costs its place among its goal's variants, divided by W, more) gains a little
  on the calculus (140 with W = 200, against 134) and loses on set.mm (59 against 66);
  with `guided` it loses on both (165 and 96). The atom stays, not recommended: a proof
  that needs a variant of a low place is put back too far.

### The agent bench: Whitehead against MM1 (2026-10-17)

**The question, the author's hypothesis:** an agent that proves with the mechanical
engine below it, Whitehead, spends less time and fewer tokens than one that proves the
default way, writing MM1. The expected price is memory: Whitehead's trees are large.

**The bench** (`bench/agents/`):
- **Two agents,** `claude -p`, each in a directory of its own, with the same model
  (Sonnet 5.5), effort (high) and limits (150 turns, $5, 40 minutes):
  - `whitehead`: the MCP server of Whitehead on peano, with `tactics/`;
  - `mm1`: `./check`, which puts the agent's proof after the theorem's header at the end
    of the library and compiles it with `mm0-rs`, a hole `_` showing its goal.
  - Both: `library.mm1`, the library up to the theorem, and `./search`, a search of it.
  - Nothing else. The user's settings, skills and other MCP servers are not loaded. A
    file outside the directory, other shell commands and the web are denied.
- **The tasks:** ten theorems of `peano.mm1`, of 3 to 48 steps in the known proof
  (`tasks.json`), chosen so that their statements use no local definition, which the
  server could print but not read: `mt2`, `bibi1`, `eor`, `sucsub`, `notfal`,
  `mulmoddir`, `ssasym`, `addcom`, `dvdasymd`, `divmod`. `guided` alone proves the
  first in 2 s, none of the others.
- **Measured:**
  - the agent: tokens (input, cache writes, cache reads, output), cost, turns, time,
    tool calls, from the transcript;
  - the cost is the tokens at the model's list prices (Sonnet 5.5: $2 input, $10
    output, $0.20 cache reads per million, a cache write 2 times the input for an
    hour). The CLI's own `total_cost_usd` is kept beside it: Claude Code 2.1.148 priced
    Sonnet 5.5 at $5 / $6.25 / $0.50 / $25, which reproduces every run to $0.001, so its
    figures were 2.2 times too high, and its `--max-budget-usd` of $5 was $2.20;
  - the machine: the server's CPU time and largest resident memory, by `/usr/bin/time`,
    or the same summed over every `./check`.
- **Accepted by `mm0-rs` in both cases:**
  - Whitehead's proof, through the server's new `--export`: `proof` writes the `.mmb`
    with the proof found put in;
  - the agent's `.mm1`, compiled again by the bench.
- **Made for it in Whitehead:**
  - a theorem that the specification leaves out, as `peano.mm0` leaves out all but the
    `pub` ones, has its binders from the proof file, named by its index. Its statement
    then prints with its names, and patterns and intermediate goals can name them;
  - `mcp --export`;
  - the size of the known proof in the search's verbose line for every ending.

**Round 1, the library as it is.** Both proved all ten. The MM1 agent was cheaper on
every task (W/M: Whitehead's figure over MM1's):

| theorem | tokens W/M | cost W/M | time W/M | Whitehead calls | MM1 calls |
|---|---|---|---|---|---|
| `mt2` | 1.5 | 1.1 | 1.0 | 3 | 3 |
| `bibi1` | 1.4 | 0.9 | 1.1 | 3 | 3 |
| `eor` | 5.2 | 2.3 | 3.2 | 16 | 4 |
| `sucsub` | 8.1 | 3.9 | 5.3 | 31 | 7 |
| `notfal` | 3.7 | 2.1 | 2.2 | 12 | 5 |
| `mulmoddir` | 11.4 | 5.5 | 5.2 | 28 | 4 |
| `ssasym` | 12.3 | 6.3 | 4.6 | 40 | 9 |
| `addcom` | 17.5 | 8.2 | 6.6 | 65 | 5 |
| `dvdasymd` | 23.0 | 8.6 | 4.7 | 104 | 7 |
| `divmod` | 20.2 | 8.8 | 4.6 | 144 | 14 |

- **Totals:** 14.2M tokens and $4.74 for Whitehead, 1.04M and $0.81 for MM1.
- **The MM1 agent recalled:** for `mt2`, `bibi1`, `notfal` and `mulmoddir` it wrote
  the library's own proof, character for character, at its first check. The model knows
  `peano.mm1`. So this round measures recall against search.

**Round 2, the theorems renamed** (`rename.py`):
- every theorem of the library is renamed `L` and its number, in proofs, `do` blocks
  and comments, but not in formulas or strings;
- the renamed file compiles with `mm0-rs` with no error, and its `.mmb` proves the
  renamed specification;
- both agents see the same names, and the prompt no longer names the library.

| theorem | tokens W/M | cost W/M | time W/M | Whitehead calls | MM1 calls |
|---|---|---|---|---|---|
| `mt2` | 1.0 | 0.7 | 0.5 | 3 | 5 |
| `bibi1` | 0.6 | 0.4 | 0.7 | 3 | 6 |
| `eor` | 2.4 | 1.2 | 1.0 | 14 | 8 |
| `sucsub` | 5.4 | 2.8 | 3.2 | 20 | 5 |
| `notfal` | 5.3 | 3.4 | 3.8 | 20 | 7 |
| `mulmoddir` | 14.8 | 7.4 | 8.1 | 48 | 7 |
| `ssasym` | 6.6 | 3.1 | 2.9 | 32 | 7 |
| `addcom` | 39.8 | 17.7 | 27.2 | 174 | 7 |
| `dvdasymd` | 8.2 | 3.8 | 4.2 | 80 | 15 |
| `divmod` | 21.7 | 9.1 | 5.6 | 165 | 16 |

- **MM1:** proved 10 of 10, with 1.54M tokens, $1.16, 296 s of agent time, and 15 MB at
  most for `mm0-rs`.
- **Whitehead:** proved 9 of 10, with 18.2M tokens, $6.16, 1,503 s, and 2.1 GB at most
  for the server (`addcom`). On `divmod` it reached the limit, $5 in the CLI's dollars,
  $2.10 at list prices.
- **The MM1 agent's proofs now are its own:** nine of ten differ from the library's.
  `notfal` is a one-line proof. `addcom` keeps the induction of the library's. It
  needed 1 or 2 checks, after 1 to 11 searches.

**Round 2, three runs of each pair** (2026-10-18; two more runs, `results/`): the gap
holds in every run. Proved (+) or not (−), with the tokens in thousands:

| theorem | Whitehead | MM1 | median W/M |
|---|---|---|---|
| `mt2` | +75 +75 +75 | +72 +50 +53 | 1.4 |
| `bibi1` | +75 +75 +75 | +134 +149 +177 | 0.5 |
| `eor` | +327 +336 +360 | +137 +192 +89 | 2.5 |
| `sucsub` | +521 +832 +310 | +97 +148 +124 | 4.2 |
| `notfal` | +527 +254 +232 | +99 +84 +98 | 2.6 |
| `mulmoddir` | +1289 +695 +1359 | +87 +93 +90 | 14.3 |
| `ssasym` | +880 +1777 +1886 | +134 +192 +122 | 13.2 |
| `addcom` | +4827 +4743 −6530 | +121 +164 +179 | 29.4 |
| `dvdasymd` | +2731 +6136 +4231 | +334 +188 +233 | 18.2 |
| `divmod` | −6931 −6836 −6026 | +319 +556 +446 | 15.3 |

- **Proved:** Whitehead 26 of 30, MM1 30 of 30.
- **Cost at list prices:** $19.87 against $3.69.
- **Memory, at most:** 2.1 GB against 15 MB.
- **Where the Whitehead agent's calls go** (20 runs): 322 `variants`, 243 `choose`, 117
  `run`, 105 `goal`, 68 `goals`, 46 `start`. A result is short (700 characters for
  `variants`), so the cost is the calls themselves: each reads the whole context again.
  The agent chose steps one by one, as if writing the proof term a step at a time.

**Harder theorems** (`tasks-hard.json`, renamed, one run each, a limit of $10 in the
CLI's dollars, $4.40 at list prices, 200 turns, an hour):

| theorem | steps | Whitehead | MM1 | tokens W/M |
|---|---|---|---|---|
| `leasymd` | 60 | proved, 11.8M tokens, $3.13 | proved, 0.58M, $0.41 | 20.4 |
| `ltmul1` | 64 | proved, 2.5M, $0.86 | proved, 0.44M, $0.26 | 5.7 |
| `dvdadd1` | 67 | proved, 5.5M, $1.61 | proved, 0.38M, $0.25 | 14.7 |
| `prth` | 69 | proved, 8.2M, $2.33 | proved, 0.55M, $0.35 | 14.9 |
| `divlem3` | 111 | not proved, 12.8M, $3.84 | proved, 0.96M, $0.73 | 13.4 |
| `appendnth1` | 115 | not proved, 7.5M, $2.81 | proved, 1.90M, $1.03 | 4.0 |

The MM1 agent proved all six. The Whitehead agent stopped on the last two, judging the
budget left too small.

**What this means:**
- **The hypothesis does not hold here,** for this model and this interface. Whitehead
  is cheaper only where `guided` proves the theorem at once (`mt2`, `bibi1`). Past
  that, its agent spends 2 to 40 times the tokens, and more time.
- **The tokens are calls.** Both agents start from about the same context (15,400
  tokens for MM1, 18,400 for Whitehead, its tools' schemas included), and each call
  reads all of it again.
  - The MM1 agent searches for lemmas by their statements, writes a whole proof term,
    and lets MM1's elaborator fill in what unification can, in 5 to 16 calls.
  - The Whitehead agent works through the tree a step or a goal at a time: runs,
    variants, choices, intermediate goals; 14 to 174 calls.
- **MM1's elaborator already does what the engine was to do for the agent:** it decides
  the metavariables by unification. What Whitehead adds is search, and an agent that
  can name the lemmas needs little of it.
- **Memory:** Whitehead's server took 67 MB to 2.1 GB, `mm0-rs` at most 15 MB. Its CPU
  time was up to 128 s, `mm0-rs`'s under 0.1 s.
- **Caveats:**
  - three runs of each pair of the ladder, one of the harder theorems;
  - one model;
  - the model knows MM1 from its training, while it meets Whitehead's tools for the
    first time;
  - what the model remembers of the proofs' structure is not removed by the renaming;
  - set.mm is not tried here, since it has no MM1 source.
- **What it suggests for the interface:** the agent should give the engine what it is
  good at, a whole sketch, a proof term with holes or a chain of intermediate
  statements, and have the engine close the gaps by search in one call. That is a
  smaller number of calls, which is what the tokens follow.

### Whitehead as a gap filler (2026-10-18)

**The question:** does Whitehead pay as a gap filler beside an MM1 agent? The agent
writes the structure of a proof, and Whitehead fills its holes by search.

**What was built:**
- `prove goal` (`Main.lean`): a proof of a statement, under a theorem's hypotheses and
  from the assertions before it, printed as an MM1 term (`Prove/Mm1.lean`).
  - A metavariable `?a` of MM1 is one of the search's; the same name is the same one.
  - The terms come in three forms, tried in order. `short` gives the subproofs only, for
    MM1's unification to infer the variables. `bound` names the bound variables with
    `!!`. `explicit` gives every variable with `!`. A dummy is named `wd` and a number.
    A conversion is left to MM1, which unfolds definitions itself.
  - The default search is a breadth-first search to depth 2 first, then `guided`: the
    proof of one or two steps is found before a longer one that a rail would give.
  - Loading peano takes 0.2 s.
- `./fill [SECONDS]` (`bench.py`): `./check`, and more. It takes each hole whose goal,
  as `mm0-rs` prints it, has no metavariable, one at a time, since a filled hole can
  decide another's metavariables. It puts the first form of the proof found that MM1
  accepts into the hole, and writes `proof.mm1` back.
  - A goal with a metavariable is not tried: the prover would choose the metavariable
    to suit itself. `G -> ?a -> a = b` is "proved" with `?a := G -> a = b`.
- The agent `hybrid`: the MM1 agent with `./fill`, and told to write the structure and
  leave the routine steps as holes.

**Results, one run of each task,** against the MM1 agent's runs of 2026-10-17/18, under
the same limits:

| | proved | tokens | cost |
|---|---|---|---|
| ladder, hybrid | 10 of 10 | 2.67M | $1.68 |
| ladder, MM1 (the median of 3 runs, task by task) | 10 of 10 | 1.63M | $1.24 |
| harder theorems, hybrid | 6 of 6 | 9.30M | $4.57 |
| harder theorems, MM1 | 6 of 6 | 4.80M | $3.03 |

- **On the ladder the agent hardly used it:** it called Whitehead in only 3 of the 10
  tasks.
- **On the harder theorems it used it on every task.** The hybrid agent took more tokens
  on four (1.0 to 4.5 times) and fewer on `prth` (0.8).
- **The holes:** of 58 tried, 8 were filled, with proofs of 1 to 41 steps:
  - **no proof in 5 to 40 s, 38 holes.** These are arithmetic identities
    (`b * suc q + 0 = b * q + b`), facts of order and divisibility
    (`0 < c -> a < b -> a * c < b * c`), and sometimes the theorem itself;
  - **14 holes name variables of the agent's own,** the variable of an induction it
    started, which the task does not have;
  - **3 proofs were found that MM1 did not take;**
  - **2 holes were not tried,** for their metavariables.

**What this means:**
- **As a gap filler, breadth-first search does not pay either, on this library.** The
  steps that an agent leaves as holes are those it finds hard, and those are beyond the
  reach of a search that meets hundreds of variants at each node. The steps that the
  search can reach, the agent writes itself.
- **What the failed holes ask for is decision procedures, not search:**
  - normalizing arithmetic (`b * suc q + 0 = b * q + b`);
  - order and linear arithmetic;
  - propositional tautologies, which the filler did prove (`(a -> c) /\ (b -> c) -> a -> c`).

  These are the oracles of `CLAUDE.md`, layer 2: they decide a goal and give a
  certificate, with no search.
- **Not tried:** goals under the agent's own variables (extra variables in the task);
  better ranks, so that the search reaches further.

### The learned ranking layer (a plan of 2026-10-18)

**Why now:** an LLM agent pays for every call, so it should be called rarely, and at the
top ("The agent bench", "Whitehead as a gap filler"). A small learned model pays almost
nothing for a decision. Whitehead's tree is then its environment: the state is the tree,
an action is the expansion of a variant, the payoff a proof. Precedents in Metamath:
Holophrasm (Whalen, 2016) and GPT-f (Polu and Sutskever, 2020), a model scoring the next
step and a search exploring by the scores.

**What Russell has:**
- The author's dataset (`ml/learning_data.flow`, `ml/collect_data.flow`, 2021): for each
  assertion, its usage contexts, each a goal with its premises, positive where the
  known proof uses the assertion and negative where it does not.
- The models of `ml/` (centroids, medoids, LGG templates, k-NN, `premise_selector.flow`)
  were written in 2026 with Claude: ideas, not the reference.

**What is learned, in order:**
1. **A scorer of variants:** at a goal node, how likely a variant is to be on a proof.
   This is the main one, and the data is plentiful.
2. **A scorer of rails:** for `subproofs(rank=...)`. The features are those of
   `prove rails --dump`, which beat occurrences offline ("Ranks for the rails").
3. **A value of goals,** later: how likely a goal is to be proved within a budget, from
   the searches' own logs.

**Where it plugs in, with no change to the engine:**
- a cost, `depth(by=model)`: a step costs 1 and `λ·log(p_max / p)`, where p_max is that of
  the best variant at its goal. The first variant costs nothing more, so a mistake of
  the model only delays. The cost is still at least 1 a step, so `search` stays fair
  (completeness, "Composable tactics");
- for agents: a filter, `top(N, by=model)`, and an order of `variants`;
- for rails: `rank=model`.

**The data** (`prove export`, to build):
- For each theorem, the full expansion along its known proof, as `oracleAll` makes it
  and `prove variants` already walks: at each goal node of the path, every variant, the
  known proof's labelled positive.
- Negatives subsampled: all those that pass the known variant's shape filter (the hard
  ones), and a sample of the rest.
- Later, positives also from the proofs that the search finds.
- **No leakage:** the theorems are split in the order of the file, the first 80% to train
  on, then 10% to tune, then 10% to test. Every feature that counts proofs (uses,
  recency, co-occurrence) counts only those before the theorem.
- **Size:** every 40th theorem of set.mm gave 50,294 nodes of 983 variants at the median
  ("Measurement"), so all of set.mm, with 50 variants kept a node, makes some 50 million
  rows. A sample of theorems will do at first.

**The features,** computed by one Lean function for both the export and the search, so
that the model is served what it was trained on:
- **the step:** its uses before the theorem, its recency, its number of premises, the
  sizes of its new goals, whether they are ground, bare or a premise (`hyp`), the
  metavariables it brings, how specific its conclusion is;
- **the goal:** its depth, size and head term;
- **the pair:** the symbols the goal shares with the assertion's conclusion and premises,
  weighted by their rarity;
- **the theorem:** a prior for each assertion, from the earlier theorems whose statements
  share symbols with this one (k-NN), and P(assertion | symbols) (naive Bayes), as
  Sledgehammer's MaSh does for premise selection. It is computed once per theorem.

**The models,** each in turn and only while the one before it is beaten offline:
- M0, the baseline: the hand ranks, by uses and by recency. The known variant comes first
  at 8.2% and 10.4% of the nodes.
- M1: linear, trained per node by a softmax over the node's variants, as in the rails'
  analysis; numpy.
- M2: gradient-boosted trees, a ranking objective. Trees are evaluated in Lean in a few
  lines.
- M3, later: a small neural scorer over the expressions' structure.
- The value of goals, later.

**Tooling:**
- Lean exports the data and evaluates the models.
- Python trains them (numpy and scipy are installed; LightGBM for M2 is to install).
- A model is a JSON file that Lean reads (`Whitehead/Json.lean`).
- A test checks that Lean's scores are Python's on a sample.

**Evaluation,** at three levels:
- offline: where the known variant ranks on the test theorems (first, first 5, first 10,
  mean reciprocal rank), and by depth;
- in search: the theorems proved at 1 s and 5 s on held-out samples, against `bfs` and
  `guided`; the CPU per proof, and the time the model takes;
- ablations, by feature group.

**Then a loop, expert iteration:** search the training theorems with the model. The
proofs it finds, other than the known ones, are new positives. Train again, while the
proofs found grow. That is the part of reinforcement learning to try first. A search
with a value of goals (Monte Carlo tree search) comes after.

**Order of building:**
1. `prove export`, with the split; the number of rows and positives.
2. The offline evaluator, which gives again 8.2% (uses) and 10.4% (recency).
3. The theorem prior (k-NN, naive Bayes), offline.
4. M1, offline. The mark to beat: the known variant in the first 10 at 36.7% of the
   nodes (recency).
5. The model in Lean, the cost atom, the parity test.
6. Search, against `guided`. The model goes in only if it proves more.
7. M2, the value of goals, expert iteration.

**Questions, and the author's answers (2026-10-18):**
1. Training in Python, inference in Lean? Everything in Lean is possible for M1 and M2,
   at the price of writing the trainers. The author asked what Python brings:
   - LightGBM's ranking objectives, and PyTorch on the GPU for M3; Lean has neither;
   - models changed without rebuilding Lean;
   - optimizers that are tested, rather than trainers of our own.

   Its price is two languages, and a model that Lean must evaluate as Python does. The
   features are computed by Lean alone, and a test checks the scores. The prover runs
   without Python: it is needed for training only.
2. The corpus: **every MM0 file at hand.** The files contain one another, so each theorem
   is taken once (by its name, `.tools/learn/names`):
   - peano is in peano_hex, which is in mm0 and in x86;
   - x86 is in compiler, which is in hello_mmc and hello_assembler;
   - so: set.mm (47,589), hello_mmc (10,134: peano, peano_hex, x86, compiler and its
     own), mm0's own (1,085), hol (99), set (26, a small example of its own), and
     hello_assembler's own (6). About 58,900 proofs.

   The features mean the same in every file, so one model can serve them all. The split
   is made in each file.
3. LightGBM may be installed: it is, in `.tools/venv` (4.7.0, with numpy and scipy;
   Python 3.14). The machine has a GPU after all, a GeForce RTX 4060 with 8 GB, for M3.

**Built: the data** (`prove export`, `Prove/Features.lean`, `Prove/Dataset.lean`):
- **The columns:** the theorem (number and name), the goal node, the label, the
  assertion (−1 for a conversion), the node's number of variants, and 23 features.
- **The draw:** 50 negatives a node by default (`--negatives`, 0 for all), fixed by the
  node.
- **Writing:** numbers with four significant digits, so peano's data is 108 MB.
- **peano:** 2,700 theorems in 6 s, 1,313,001 rows, 29,050 nodes with their known
  variant. 50 proofs are left out, with a shared conversion that the skeleton reader
  does not take.
- **The corpus** (`.tools/learn/export-all.sh`):
  - set.mm: 68,598,966 rows and 1,345,329 nodes, in 32 minutes on 20 threads;
  - its test theorems with all their variants (every 10th from 42,850): 618 theorems,
    76,160,788 rows, 16,631 nodes, a median of 1,076 variants a node (a mean of 4,579);
  - the others: hello_mmc 7.0M rows, mm0 2.2M, hol and set small.

**Built: training and models** (`learn/`, Python in `.tools/venv`):
- `data.py` reads the data in batches with pyarrow, and caches it as `.npz`.
- `train.py` trains the linear model (L-BFGS, on 5M rows at most) and the trees
  (lambdarank, early stopping), on 30% of each file's training theorems (with
  `--sample-train`). 6 minutes on the whole corpus.
- `evaluate.py` gives the known variant's place among all the variants of a node, a tie
  counted as the average place.
- `parity.py`: Lean's scores (`prove score`) against Python's. The largest difference over
  20,000 rows is 5e-7, the printing of the scores, for trees and linear alike.

**Offline, among all the variants** of set.mm's test theorems (16,631 nodes):

| model | first | in the first 5 | in the first 10 | MRR |
|---|---|---|---|---|
| by uses | 6.1% | 19.4% | 27.0% | 0.135 |
| by recency | 9.4% | 28.2% | 40.6% | 0.193 |
| linear | 18.6% | 40.9% | 53.0% | 0.296 |
| trees (846) | 22.3% | 46.0% | 58.4% | 0.339 |
| trees, the first 100 | 20.4% | 44.9% | 58.1% | 0.325 |

- The trees put the known step first 2.4 times as often as recency.
- 100 trees rank nearly as well as 846, at an eighth of the cost.
- Their gains: recency 42%, uses 14%, never used 9%, how specific the conclusion is 7%,
  the shared weight of symbols 4%.

**In search** (`prove search --model trees-100.json`; the test parts only, which the
model has not seen):
- **Speed decides:** at a new goal, every variant is scored, a median of about a
  thousand.
  - With 846 trees, a search expands 2 nodes in a second at the median, where `bfs`
    expands 42.
  - With 100 trees it is 8 times faster. At 1 s, `guided` with the model's order proved
    71 theorems with 846 trees, 73 with 200, 79 with 100 (width 10).
  - The width that divides a place into a cost: 3 gave 78, 5 gave 81, 10 gave 79, 20
    gave 75.
- **A step without premises must not wait for its place.** On the compiler's theorems
  the model ranked low the lemmas that prove a goal in one step, and the search lost a
  third of what `bfs` proves (342 against 501).
  - Putting every such step first floods mm0, where there are many (169 against 233).
  - Capping its place at the width gives 399 on the compiler.
  - What works is a composition: first, at the root, the variants without premises
    (`bfs(filter=premises(0), depth=1)`: 505 of 505), then the rest. A whole first round
    of `bfs` instead takes the whole second on set.mm, whose root has thousands of
    variants.
- **`learned`** (`tactics/learned.tac`): `seq(bfs(filter=premises(0), depth=1),
  first(the closing rails, the open rail, search(depth(follow, penalty=2, by=model,
  width=5))))`.

| test part | per theorem | `bfs` | `guided` | `learned` |
|---|---|---|---|---|
| set.mm (618) | 1 s | 25 | 61 | **82** |
| set.mm | 5 s | 29 | 67 | **102** |
| the compiler, hello_mmc (505) | 1 s | 501 | 496 | **505** |
| | 5 s | 505 | 503 | 505 |
| mm0's own (491) | 1 s | 102 | 244 | 233 |
| | 5 s | 247 | 248 | 238 |

- **On set.mm:** `learned` proves 21 more than `guided` at 1 s and 35 more at 5 s, and
  loses none; +52% at 5 s, and 3.5 times `bfs`. Its proofs have 3 steps at the median,
  104 at most.
- **On mm0** it loses 4 to 5%: the model learned mostly from set.mm (89% of the rows).
- **The verifier** rejected no proof.

**Next:**
- training that weighs the files evenly, for mm0;
- features that are cheaper to compute, so that more nodes are expanded in a second;
- expert iteration: the proofs that `learned` finds, other than the known ones, are new
  positives;
- the value of goals.

### Mining and ranking (the design of 2026-10-13)

What follows is the first design, kept as it was written. The author's answers above
replace it: chains are rails, not derived theorems, and "macro-actions" are dropped.
Ranking is a filter atom (`used`), and the dataset comes from the oracle runs and the
session traces.

#### What Russell has

Two layers, of different standing (`CLAUDE.md`: the Russell source is the final judge,
but what Claude Code wrote there is not the author's word).

- The author's own, from 2021: `ml/common_subproofs.flow` and `ml/collect_data.flow`
  ("machine-learning stubs are added", "common subproofs coverage is started").
  `ruCollectSubproofCoverage` takes every use of an assertion across all proofs
  (`RuAssUsage`: theorem, proof, step) and, for the deepest step not yet covered, walks
  up its chain of parents, keeping the uses whose chains of parents are the same
  assertions (`ruFindMaxCommonPath`); the chain with its evidences is one
  `RuProofNodesCoverage`, and the command prints the distribution of chain lengths.
  `ruCollectLearningDataFromTheorem` runs the prover on a theorem with a tactic that
  follows the known proof (`compute_leafs`) and records, for every assertion node that
  the tree makes, a context: the goal expression and the premises, positive when the
  node is a step of the known proof and negative otherwise (`RuUsageContext`,
  `RuAssertionUsage` in `learning_data.flow`).
- From May 2026: `tactics/subproof_replay.flow` (`ruBuildStepIndex`, an index of the
  conclusion of every step of every proof; `spr`, the replay of a corpus subproof
  whose step matches a leaf), `tactics/linear_guided.flow` (`ruExtractSpine`: the path
  of a proof tree from a step whose conclusion unifies with the goal down to a step
  whose conclusion unifies with a premise, the steps off the path becoming open goals;
  `linear-guided`: its replay through `follow_proof`), `unify/lgg.flow` (the least
  general generalization of two expressions, a fresh variable at every mismatch;
  `ruLggDistance`; 1-gram feature vectors), and the per-assertion models of `ml/`
  (feature centroids, medoids, iterated LGG templates, k-NN, each from the positive and
  negative contexts; `ml/premise_selector.flow` scores a node by them and `ruMlTactic`
  expands the frontier best first; `commands/eval_ranking.flow` measures top-k and the
  mean reciprocal rank by replaying proofs). `commands/find_linear_chains.flow` counts
  the theorems with a spine of a given depth, offline.

#### The model for MM0

A **chain** is a path of `k` steps in a proof tree, each proving one hypothesis of the
one above it (`Chains.lean`). With the positions it is a derived rule: compose the
assertions along it by unification — the conclusion of `a₂` with the `j₁`-th hypothesis
of `a₁`, and so on down — and the result has as hypotheses what is left open along the
chain, and as conclusion that of `a₁` under the composed substitution. The rule is
applied to a goal by one unifier, as an assertion is, and is emitted as the `k` steps it
stands for: the tree is a search space, the MM0 proof is emission (as "Unfolding as an
inference step"). Russell does not build the rule: `linear-guided` replays the concrete
steps of one occurrence, instantiated by the goal; `common_subproofs` counts chains
without positions.

**Mining** (built: `prove chains`): the chains of 2 to `K` steps that occur at least
`min` times across the proofs of a file, counted in the manner of Apriori — a chain is
counted only where its upper part is frequent, since a chain occurs at most as often as
any part of it — so the counts of the frequent chains are exact and memory holds those
only. The report gives, by length, the occurrences, the distinct frequent chains, the
most frequent by name, how many occurrences reach the root of their proof and how many
start at a hypothesis of the theorem; and the coverage: the share of all steps that lie
on a chain occurring at least 2, 10, 100 or 1,000 times. A shared subproof is walked
each time it is used. The numbers are in `STATUS.md`.

**Schemas by anti-unification** (to build): the occurrences of a chain differ in what
the goal and the open hypotheses are instantiated with. Their least general
generalization (`lgg.flow`: the two expressions walked together, a fresh variable where
they differ; for MM0, a variable of the sort where the sorts agree) is the schema of the
chain: more special than the composed rule where the chain is always used with the same
subterm, and the same otherwise. The schema with its frequency describes the
macro-action for a ranking; the composed rule is its unifier.

**Macro-actions in the engine** (to build): a derived rule is an assertion of the
database (`Db.asserts`, with `pseudo` saying which chain), in the index of conclusions
with the rank of the latest assertion of the chain, so that a theorem may use it only
when it may use every step of it. Expanding a node lists the macro-actions among the
variants of one step, so expansion stays granular. The tree with macro-actions is a
superset of the tree without them: completeness is kept, and a proof found through a
macro-action is one the engine could find step by step — the same proof, which the
dedup by key merges where both are found. Soundness is as for every step: the emission
writes the chain's steps, and the verifier checks them.

**Measurement** (to build): the coverage above; and out-of-sample replay — the chains
mined on the theorems before a cut, the theorems after it replayed and searched with
and without the macro-actions, and the search baseline run again with them.

**The environment and the dataset** (to build): the state of a search is the frontier
(`Env.leafs` with their variants); an action is a pair (node, variant), which a
strategy's `expand` already is. The dataset of `collect_data.flow`: for every theorem,
the prover run with the oracle strategy over the full expansion (`oracleAll`), and for
every assertion node of the tree one row — the goal expression, the premises, the
assertion, and whether the node is a step of the known proof. That is the premise
ranking dataset; it needs no new engine, only an export. A learned policy is then a
strategy that orders `expand`.

#### Questions (2026-10-13)

1. What is a linear subproof for you: any chain of steps, which is what `prove chains`
   counts, or Russell's spine — a chain from a premise of the theorem to its goal with
   the other hypotheses open? The report counts both (to the root, from a hypothesis).
2. Are the positions part of the chain? Without them, as `common_subproofs` counts, a
   chain is not a rule; with them it is. The miner keys on them.
3. The schema: the LGG of the occurrences, or the composed rule? Both are proposed
   above, with different roles; say if one is enough.
4. Macro-actions as assertions of the database with a rank, or as a kind of step of
   their own, like unfolding? The first needs nothing new in the engine.
5. Shared subproofs: an occurrence inside a shared subproof is counted each time the
   subproof is used, as Russell counts uses. On set.mm that puts `renegcli .0 pire`
   first, 11,088 uses in 74 proofs, where `adantr .0 syl` has 9,449 uses in 1,687
   proofs; the report gives both counts. Which is the frequency of a schema: uses, or
   proofs?
6. Of the 2026 Russell files (`linear_guided`, `subproof_replay`, `lgg`, the models of
   `ml/`), which are your design, to be followed, and which are to be read as ideas?
