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

## Phase 4: linear subproofs and ranking

Phase 3 was accepted on 2026-10-13. Phase 4 is the research layer of `CLAUDE.md`:
linear subproofs mined from the set.mm translation and exposed to the prover as
derived rules; an environment API for learned policies, and a dataset for premise
ranking. It is designed here before it is built, and the questions at the end come
first. Only the miner is built.

### What Russell has

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

### The model for MM0

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

### Questions (2026-10-13)

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
