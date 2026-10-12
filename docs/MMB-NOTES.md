# The `.mmb` format — our notes

This is our own description of the MMB binary proof format, written from the format
description, the formal semantics, and the reference implementation `mm0-rs`. It is meant
to be enough to re-implement the reader without opening any of them.

Sources, all in the local checkout `/home/dmitry/tools/mm0` at commit `0d414c0b`, in
order of authority:

| Short name | Files | Role |
| ---------- | ----- | ---- |
| **formal semantics** | `mm0.md`; `examples/mm0.mm0`; `mm0-lean/mm0/mm0.lean`, `mm0b.lean` | the final judge of what is valid: the language, the formal specification written in MM0, its Lean mirror, and the Lean model of the MMB stack machine |
| **mm0-rs** | `mm0-rs/components/mm0b_parser` (reader), `mm0-rs/src/mmb/import.rs`, `mm0-rs/src/elab/verify.rs` (kernel), `mm0-rs/src/mmb/export.rs` (writer) | the reference implementation; it also wrote every `.mmb` we have |
| **mmb.md** | `mm0-c/mmb.md` | the written format description |
| mm0-c | `mm0-c/*.c` | another verifier; **not** a reference (section 9) |

Where the formal semantics say nothing — file layout, framing, the index — `mm0-rs` is
followed. Where they disagree with an implementation, they win. Section 9 lists every
point on which the sources differ, what each implementation does, and what we do.

`mm0-rs` is run as `mm0-rs compile file.mmb`, which reads the file and checks every
declaration with its kernel (exit code 0 or 1). It has no command that checks a `.mmb`
against a `.mm0` file.

Sections 1–7 were checked by decoding real files with a throwaway script written from
these notes alone: `mm0-js/test/hol.mmb`, `mm0-js/test/peano.mmb`,
`examples/tutorial/03-mm1-intro.mmb`, `tests/mmb/pass/*.mmb`. Every statement, proof
stream and unify stream in them decodes and every length field matches.

## 1. Conventions

- All integers are **little-endian**, fixed width: `u8`, `u16`, `u32`, `u64`.
- A pointer is a byte offset **from the start of the file**. `p32` is a `u32` pointer,
  `p64` a `u64` pointer. A nullable pointer is null when it is `0`.
- Tables are 8-byte aligned. The two command streams are byte-aligned.
- `cstr` is a NUL-terminated UTF-8 string.
- Identifiers: sorts, terms and theorems are referred to by **index** in order of
  declaration (`sort_id` < 128, `term_id`, `thm_id` are `u32`). Names exist only in the
  optional index (section 7).

## 2. File layout

A file is a header followed by sections reached through pointers, in this order:

```
0x00  header (40 bytes)
0x28  sort table            num_sorts bytes, then zero padding to a multiple of 8
      term table            num_terms entries of 8 bytes          <- p_terms
      theorem table         num_thms entries of 8 bytes           <- p_thms
      term data, thm data   one block per entry                    <- each entry's p_data
      proof stream          byte-aligned, ends with END           <- p_proof
      index payload         names, variable names, ...
      index                 the index header itself comes last     <- p_index
```

`mm0-rs` requires this order when it opens a file (`Header::check`):

- `40 + num_sorts <= p_terms`;
- `p_terms + 4 * num_terms <= p_thms` and `p_thms + 4 * num_thms <= p_proof` (the factor
  is 4 in the code although an entry is 8 bytes; the tables are bounds-checked exactly
  afterwards);
- `p_proof <= file size`;
- `p_index = 0`, or `p_proof < p_index <= file size`.

It also requires `p_terms`, `p_thms`, `p_index` and the pointer of the `Name` index table
to be multiples of 8, because it reads those tables in place through 8-aligned types. The
`p_data` blocks need no alignment (the writer aligns them to 8 anyway).

### Header

| Offset | Size | Field | Meaning |
| ------ | ---- | ----- | ------- |
| 0  | 4 | `magic` | the bytes `4D 4D 30 42` = `"MM0B"` (as a `u32`: `0x42304D4D`) |
| 4  | 1 | `version` | `1` |
| 5  | 1 | `num_sorts` | number of sorts, at most 128 |
| 6  | 2 | `reserved` | `0` |
| 8  | 4 | `num_terms` | number of `term`s and `def`s together |
| 12 | 4 | `num_thms` | number of `axiom`s and `theorem`s together |
| 16 | 4 | `p_terms` | `p32` to the term table |
| 20 | 4 | `p_thms` | `p32` to the theorem table |
| 24 | 4 | `p_proof` | `p32` to the proof stream |
| 28 | 4 | `reserved2` | `0` |
| 32 | 8 | `p_index` | `p64?` to the index, `0` if there is none |
| 40 | `num_sorts` | `sorts` | the sort table |

### Sort table

One byte per sort, a bit set of modifiers:

| Bit | Value | Modifier |
| --- | ----- | -------- |
| 0 | 1 | `pure` — no term may have this sort as its result |
| 1 | 2 | `strict` — no bound or dummy variable may have this sort |
| 2 | 4 | `provable` — hypotheses and conclusions must have a sort with this bit |
| 3 | 8 | `free` — no dummy variable may have this sort |
| 4–7 | | unused, `0`; `mm0-rs` rejects a sort that has any of them set |

### The `arg` word

Binders and return types are `u64` values:

| Bits | Field | Meaning |
| ---- | ----- | ------- |
| 0–54 | `deps` | bit `j` set: depends on the `j`-th **bound** variable of the declaration |
| 55 | `reserved` | `0` |
| 56–62 | `sort` | the sort id |
| 63 | `bound` | `1` for a bound variable (`{x: s}`), `0` for a regular one (`(ph: s x)`) |

Bound variables are numbered separately from arguments: the `j`-th bound variable is the
`j`-th argument that has the `bound` bit, counting from 0. The well-formedness rules
(checked by the verifier, not by decoding):

- a bound variable's `deps` is exactly its own bit, `1 << j`;
- a regular variable's `deps` may only name bound variables declared **before** it;
- a return type has `bound = 0`.

Since bit 55 is reserved, a declaration can have at most 55 bound variables, dummies
included.

### Term table

`num_terms` entries of 8 bytes at `p_terms`:

| Offset | Size | Field | Meaning |
| ------ | ---- | ----- | ------- |
| 0 | 2 | `num_args` | number of arguments |
| 2 | 1 | `sort` | bits 0–6: result sort; bit 7: `1` if this is a `def` |
| 3 | 1 | `reserved` | `0` |
| 4 | 4 | `p_data` | `p32` to the term data |

Term data at `p_data`:

| Size | Field | Meaning |
| ---- | ----- | ------- |
| `8 * num_args` | `args` | one `arg` word per argument |
| 8 | `ret` | the return type as an `arg` word; its sort equals the entry's `sort` |
| varies | `unify` | **only if the def bit is set**: a unify stream, starting right after `ret` |

`unify` is not a pointer: the table in mmb.md says `p32<unify_stream>`, but the stream is
stored inline, immediately after `ret`. Both implementations read it there, and so do the
real files.

### Theorem table

`num_thms` entries of 8 bytes at `p_thms`:

| Offset | Size | Field | Meaning |
| ------ | ---- | ----- | ------- |
| 0 | 2 | `num_args` | number of expression arguments (variables, not hypotheses) |
| 2 | 2 | `reserved` | `0` |
| 4 | 4 | `p_data` | `p32` to the theorem data |

Theorem data at `p_data`: `8 * num_args` bytes of `arg` words, then a unify stream
inline. There is no return type and **no hypothesis count**: the number of hypotheses is
the number of `UHyp` commands in the unify stream.

## 3. Commands

Both streams are sequences of `(cmd, data)` pairs in a variable-length encoding of 1, 2,
3 or 5 bytes. In the first byte, bits 0–5 are the opcode and bits 6–7 select the width
of `data`:

| First byte | Total size | `data` |
| ---------- | ---------- | ------ |
| `00xxxxxx` | 1 | `0` |
| `01xxxxxx` | 2 | the next byte |
| `10xxxxxx` | 3 | the next 2 bytes, little-endian |
| `11xxxxxx` | 5 | the next 4 bytes, little-endian |

The encoding is not canonical: `data = 0` may be written in any width. Writers use the
shortest; a reader must accept all. A command must lie inside the file; nothing more is
required to read it.

In the low bit of the opcodes that come in pairs (`0x10/0x11`, `0x14/0x15`,
`0x30/0x31`), `1` means "and save".

**Padding for writers.** mmb.md asks that every `END` start at least 5 bytes before the
end of the file "to permit read-ahead", so a file without an index ends with 4 bytes of
padding after the last `END`. `mm0-rs` writes that padding and does not require it when
reading; mm0-c refuses a file without it. A reader need not check it; a writer must
produce it.

## 4. Unify streams

A unify stream describes an expression (a `def`'s value) or a statement (a theorem's
conclusion and hypotheses) as a pattern in **prefix** order. It ends with `END`.

| Opcode | Name | `data` | Meaning |
| ------ | ---- | ------ | ------- |
| `0x00` | `END` | 0 | end of stream |
| `0x30` | `UTerm` | `term_id` | a term application; its `num_args` subpatterns follow |
| `0x31` | `UTermSave` | `term_id` | same, and the matched subterm gets the next heap index |
| `0x32` | `URef` | `heap_id` | a back-reference to heap entry `heap_id` |
| `0x33` | `UDummy` | `sort_id` | a new dummy variable of that sort; it gets the next heap index (only in a `def`) |
| `0x36` | `UHyp` | 0 | a hypothesis follows (only in an `axiom`/`theorem`) |

Heap numbering: indices `0 .. num_args-1` are the declaration's arguments, in order.
Every `UTermSave` and `UDummy` appends one entry, in stream order.

Shape:

- `def`: exactly one expression, then `END`.
- `axiom`/`theorem` with hypotheses `h1 ... hn` and conclusion `c`:
  `<c> UHyp <hn> UHyp <h(n-1)> ... UHyp <h1> END` — the conclusion first, the hypotheses
  in **reverse** declaration order.

An expression is `URef i`, or `UDummy s`, or `UTerm[Save] t` followed by as many
expressions as `t` has arguments. The grammar is self-delimiting, so a decoder can
recover the tree (and the hypothesis count) from the stream and the term table. This is
how `mm0-rs` reads it: it builds the tree directly and rejects a stream that ends early,
has commands left over, refers to a heap index that does not exist yet, or has a `UHyp`
inside an expression.

`UTermSave` takes its heap index *before* its arguments are read, so a stream can
describe a cyclic term (`UTermSave 0, URef <itself>`). Such files are invalid. `mm0-rs`
rejects a reference to a saved term that is still being read ("cyclic reference"); the
stack machine of mmb.md rules it out by checking a def's unify stream against the value
its proof stream builds.

## 5. Proof stream

The proof stream at `p_proof` has two levels: a sequence of **statements**, each of which
may contain a sequence of **proof commands**.

### Statements

A statement is a command whose `data` is the distance in bytes from the start of this
statement to the start of the next one. The stream ends at a command with opcode `0`.

| Opcode | Name | Body | Needs a `.mm0` statement | Consumes |
| ------ | ---- | ---- | ------------------------ | -------- |
| `0x04` | `Sort` | none | `sort` | next sort |
| `0x05` | `Term` / `Def` | proof commands iff the term-table entry has the def bit | `term` or `def` | next term-table entry |
| `0x0D` | `LocalDef` | as `0x05` | none | next term-table entry |
| `0x02` | `Axiom` | proof commands | `axiom` | next theorem-table entry |
| `0x06` | `Thm` | proof commands | `theorem` | next theorem-table entry |
| `0x0E` | `LocalThm` | proof commands | none | next theorem-table entry |

Bit 3 (`0x08`) is the "local" flag. Statements are not numbered: the `k`-th statement of
a class refers to the `k`-th entry of the corresponding table. At the end of the stream
all three counters must equal `num_sorts`, `num_terms`, `num_thms`.

Framing:

- `data` must not be smaller than the statement command itself;
- a statement without a body (`Sort`, and `Term` on an entry without the def bit) has
  `data` equal to its own encoded size;
- a statement with a body is followed directly by proof commands and one `END`, and
  `data` points exactly past that `END`. `END` is recognized by its opcode (the low six
  bits of the byte).

Whether `0x05` is a `term` or a `def` is decided by the def bit of the table entry, not
by the opcode. `0x0D` on an entry without the def bit would be a term that the `.mm0`
file does not declare; that is not valid (section 9, point 7).

### Proof commands

| Opcode | Name | `data` | Effect (summary) |
| ------ | ---- | ------ | ---------------- |
| `0x00` | `END` | 0 | end of this statement's proof |
| `0x10` | `Term` | `term_id` | pop the arguments, push the term |
| `0x11` | `TermSave` | `term_id` | `Term`, then `Save` |
| `0x12` | `Ref` | `heap_id` | push heap entry; or discharge an obligation against a saved conversion |
| `0x13` | `Dummy` | `sort_id` | new dummy variable; push it and save it |
| `0x14` | `Thm` | `thm_id` | apply a theorem |
| `0x15` | `ThmSave` | `thm_id` | `Thm`, then `Save` |
| `0x16` | `Hyp` | 0 | turn the expression on top into a hypothesis |
| `0x17` | `Conv` | 0 | `e1, ⊢ e2  →  ⊢ e1, e1 =?= e2` |
| `0x18` | `Refl` | 0 | discharge `e =?= e` |
| `0x19` | `Symm` | 0 | `e1 =?= e2  →  e2 =?= e1` |
| `0x1A` | `Cong` | 0 | split `t es =?= t es'` into one obligation per argument |
| `0x1B` | `Unfold` | 0 | unfold a definition on the left of an obligation |
| `0x1C` | `ConvCut` | 0 | `e1 =?= e2  →  e1 = e2, e1 =?= e2` |
| `0x1E` | `ConvSave` | 0 | pop `e1 = e2` and save it |
| `0x1F` | `Save` | 0 | save the top of the stack without popping it |
| `0x20` | `Sorry` | 0 | admit a goal; never part of a valid proof (section 9, point 6) |

Opcode `0x1D` is unassigned. The `data` of `Dummy` and `UDummy` must fit in a byte.
Proofs are in **postfix** order: arguments first, then the constructor.

Opcodes seen in the well-formed files we have: all of the above except `Sorry`; `data`
widths 0, 1 and 2 bytes.

## 6. What the commands mean

The reader only decodes; this section is what the `dump` output has to be understood
against, and it is the starting point for phase 2. The machine is the one described in
mmb.md and modelled in `mm0b.lean`. Each rule is stated the way the formal semantics
require; `mm0-rs` implements the same rules, on a different representation (it first
turns the command stream into a proof DAG in `import.rs`, then checks the DAG in
`verify.rs`). Where mm0-c or `mm0-rs` does something else, section 9 says so.

### Machine state

- **store** — the expression nodes built so far in the current statement. Two nodes are
  *the same expression* only if they are the same node: equality is identity, never
  structural comparison. `Term 0, Term 0` builds two different nodes. (mmb.md says so
  explicitly; `mm0b.lean`, `mm0-rs` and mm0-c all work this way.)
- **stack** `S` — elements are one of: `expr e`; `proof e` (written `⊢ e`); a conversion
  `e1 = e2`; an obligation `e1 =?= e2`.
- **heap** `H` — `expr`, `proof` or conversion elements, addressed by index.
- **hyps** `HS` — the hypotheses declared so far (theorems only).
- **next_bv** — how many bound variables exist; the next dummy gets this bit.

Each node carries a sort, a `bound` flag (true only for bound variables and dummies), and
a set of bound variables `deps(e)`, represented as 55 bits.

At the start of every statement the store, stack and hyps are emptied and the heap is
loaded with one variable node per argument, checking the `arg` rules of section 2 against
the sorts declared **so far**, and that no bound variable has a `strict` sort.

### Proof commands

`Term t` / `TermSave t` — `t` must be less than the number of terms declared so far (no
forward or self reference). Pop `num_args` elements, all of which must be `expr`. For
argument `i` with binder `a_i`: the sorts must be equal, and if `a_i` is bound then the
argument must be a bound variable. The new node has the term's result sort,
`bound = false`, and its `deps` depend on what is being checked:

```
in an axiom or theorem (the variables of the term; `HasVar` in mm0.mm0):
  deps(t e1 ... en) = deps(e1) ∪ ... ∪ deps(en)            all arguments

in a definition (the free variables of the term; `Free` in mm0.mm0):
  deps(t e1 ... en) = union over the REGULAR arguments i of
                        deps(e_i) minus deps(e_j) for each bound argument j
                                              that a_i is declared to depend on
                    ∪ union of deps(e_j) for the bound arguments j
                        that the return type is declared to depend on
```

`Ref i` — `i` must be in range. If `H[i]` is a conversion `e1 = e2`, pop an obligation
and require it to be exactly `e1 =?= e2`. Otherwise push `H[i]`.

`Dummy s` — `s` must be a declared sort that is neither `strict` nor `free`; `next_bv`
must be below 55. Create a bound variable with `deps = {next_bv}`, increment `next_bv`,
push the variable on the stack and on the heap.

`Thm T` / `ThmSave T` — not allowed in a definition. `T` must be less than the number of
theorems declared so far. With `n = num_args`, the stack must look like

```
... , ⊢ h1, ..., ⊢ hm,   e1, ..., en,   e
      subproofs          substitution   the claimed conclusion
```

Pop `e`, then `e1 ... en`. For each `i`, with binder `a_i` and `d = deps(e_i)`:

- sorts equal, and bound binders take bound variables, as for `Term`;
- if `a_i` is bound: `d` must be disjoint from `deps(e_k)` for **every** earlier argument
  `k < i`; remember `d` as the dependency set of this bound variable;
- if `a_i` is regular: for every bound variable `j` seen so far that `a_i` is **not**
  declared to depend on, `d` must be disjoint from that variable's set.

Then run the theorem's unify stream in mode `UThm` with heap `[e1 ... en]` and target
`e`; this pops the `m` subproofs. Push `⊢ e`.

`Hyp` — not allowed in a definition. Pop `expr e`, whose sort must be `provable`; append
`e` to the hyps and `⊢ e` to the heap.

`Conv` — pop `⊢ e2`, pop `expr e1`; push `⊢ e1`, push `e1 =?= e2`.
`Refl` — pop `e1 =?= e2`; the two must be the same node.
`Symm` — pop `e1 =?= e2`; push `e2 =?= e1`.
`Cong` — pop `e1 =?= e2`; both must be applications of the same term; push
`a_n =?= b_n`, ..., `a_1 =?= b_1` (the first argument ends up on top).
`Unfold` — pop `expr e`, pop `(t e1 ... en) =?= e'`; `t` must be a `def`; run `t`'s unify
stream in mode `UDef` with heap `[e1 ... en]` and target `e`; push `e =?= e'`.
`ConvCut` — pop `e1 =?= e2`; push `e1 = e2`, push `e1 =?= e2`.
`ConvSave` — pop `e1 = e2`; append it to the heap.
`Save` — the top must not be an obligation; append a copy of it to the heap.
`Sorry` — not a valid command: a proof that contains it is rejected.
`END` — stop; the caller checks the result.

### Unify commands

The unifier has its own stack, initially `[target]`, and its own heap, initially the
substitution. It runs in one of three modes.

| Mode | Used by | Heap | Target |
| ---- | ------- | ---- | ------ |
| `UThm` | `Thm`, `ThmSave` | the substitution `e1 ... en` | the claimed conclusion |
| `UDef` | `Unfold`, and the end of a `def` | the term's arguments | the unfolded / defined value |
| `UThmEnd` | the end of an `axiom`/`theorem` | the declaration's own variables | the proved statement |

- `URef i` — pop `e`; it must be the same node as heap entry `i`.
- `UTerm t` / `UTermSave t` — pop `e`; it must be an application of `t`; push its
  arguments so that the first is on top; if saving, append `e` to the heap, marked
  *saved*.
- `UDummy s` — only in `UDef`. Pop `e`; it must be a bound variable of sort `s`; its
  `deps` must be disjoint from the arguments and from the earlier dummies (the heap
  entries not marked saved); append it to the heap.
- `UHyp` — in `UThm`: pop `⊢ e` from the **main** stack, push `e`. In `UThmEnd`: the
  unify stack must be empty; pop the most recent entry of `HS`, push it. In `UDef`: error.
- `END` — the unify stack must be empty; in `UThmEnd` the hyps must also be used up.

### End of a statement

- `Sort`: the counter must be below `num_sorts`.
- `Term`/`Def`/`LocalDef`: result sort declared and not `pure`; `ret` checked like an
  argument, and its sort must equal the sort in the table entry. For a def: run the body;
  the stack must hold exactly one `expr e`; `sort(e)` must equal the result sort;
  `deps(e)` must be a subset of `ret.deps`; then unify in mode `UDef` against the def's
  own stream.
- `Axiom`/`Thm`/`LocalThm`: run the body; the stack must hold exactly one element, an
  `expr e` for an axiom and a `⊢ e` for a theorem; `sort(e)` must be `provable`; then
  unify in mode `UThmEnd`.
- After the last statement: the three counters must equal the counts in the header.

Every statement that is not local is matched against the next statement of the same kind
in the `.mm0` file. That step is defined by the formal specification (the environment
built from the proof file must *extend* the one built from the `.mm0` file: `env.extend`
in `mm0.lean`). It is phase-2 material and is not described here.

## 7. The index

The index is optional. It holds names and notation, and nothing in it affects whether a
proof is valid. `mm0-rs` nevertheless checks its structure when it opens a file, and
refuses a file whose index is damaged.

At `p_index`: a `u64` count `num_entries`, then that many 16-byte entries.

| Offset | Size | Field |
| ------ | ---- | ----- |
| 0 | 4 | `type` — four ASCII bytes |
| 4 | 4 | `data` — depends on the type |
| 8 | 8 | `ptr` — `p64` to the table |

Entries of an unknown type are skipped. A known type may occur only once. The tables we
read:

**`"Name"`** — `num_sorts + num_terms + num_thms` entries of 16 bytes, sorts first, then
terms, then theorems: `proof` (`p64?`, the statement in the proof stream that declares
the item) and `name` (`p64?<cstr>`).

**`"VarN"`** — `num_terms + num_thms` entries of 8 bytes, each a `p64?` to a string list.
A string list is a `u64` count followed by that many `p64?<cstr>`. The list names the
arguments in order and continues with the dummies, in the order of the `Dummy` commands
of the proof (which is also the order of the `UDummy` commands). An anonymous binder is
stored as the name `_`.

**`"HypN"`** — `num_thms` entries of 8 bytes, each a `p64?` to a string list naming the
hypotheses in the order of the `Hyp` commands.

What is an error and what is not, following `mm0-rs`:

- an error: the index header or its entries do not fit in the file; one of the three
  tables above does not fit in the file at its `ptr`; a table type occurs twice;
- not an error: a missing table; a name pointer that is null, out of range, or not valid
  UTF-8; a string list that is missing or too short. The item then gets a generated name:
  `s3` for a sort, `t5` for a term, `T7` for a theorem, `v0` for a variable, `h0` for a
  hypothesis.

The other defined types are `"Delm"` (delimiters), `"Nota"` (notations), `"Lisp"` and
`"Deps"` (both specific to `mm0-rs`). They are specified in mmb.md; we do not need them
for phase 1 and the reader keeps their entries as raw `(type, data, ptr)` triples.
For `"Delm"` and `"Nota"` the reader checks only what `mm0-rs` checks when it opens the
file: a `Delm` table is two NUL-terminated byte runs inside the file; a `Nota` table
starts with a `p64` that lies in the file at or after the 8 bytes of that pointer itself.
These two would let `dump` print expressions in notation; that is a possible later
addition, not a planned one.

## 8. A complete small file

`tests/fixtures/disputed/regular_arg_vars.mmb` (244 bytes), for the specification

```
provable sort wff;
sort set;
term al {x: set} (ph: wff x): wff;
term p (x: set): wff;
term imp (a b: wff): wff;
axiom ax5 {x: set} (ph: wff): $ imp ph (al x ph) $;
theorem bad {x: set}: $ imp (p x) (al x (p x)) $;
```

```
00  4d 4d 30 42                magic "MM0B"
04  01                         version 1
05  02                         num_sorts 2
06  00 00                      reserved
08  03 00 00 00                num_terms 3
0c  02 00 00 00                num_thms 2
10  30 00 00 00                p_terms 0x30
14  48 00 00 00                p_thms  0x48
18  ca 00 00 00                p_proof 0xca
1c  00 00 00 00                reserved2
20  00 00 00 00 00 00 00 00    p_index: none
28  04 00                      sorts: wff = provable, set = no modifiers
2a  00 00 00 00 00 00          padding to 0x30

30  02 00  00  00  58 00 00 00    term 0 (al):  2 args, sort 0, not a def, data at 0x58
38  01 00  00  00  70 00 00 00    term 1 (p):   1 arg,  sort 0,            data at 0x70
40  02 00  00  00  80 00 00 00    term 2 (imp): 2 args, sort 0,            data at 0x80

48  02 00  00 00  98 00 00 00     thm 0 (ax5): 2 args, data at 0x98
50  01 00  00 00  b8 00 00 00     thm 1 (bad): 1 arg,  data at 0xb8

58  01 00 00 00 00 00 00 81    al.args[0]: bound, sort 1, deps {0}      {x: set}
60  01 00 00 00 00 00 00 00    al.args[1]: regular, sort 0, deps {0}    (ph: wff x)
68  00 00 00 00 00 00 00 00    al.ret:     sort 0, no deps
70  00 00 00 00 00 00 00 01    p.args[0]:  regular, sort 1              (x: set)
78  00 00 00 00 00 00 00 00    p.ret
80  00 .. (24 bytes)           imp.args[0], imp.args[1], imp.ret: all sort 0

98  01 00 00 00 00 00 00 81    ax5.args[0]: bound, sort 1, deps {0}     {x: set}
a0  00 00 00 00 00 00 00 00    ax5.args[1]: regular, sort 0, no deps    (ph: wff)
a8  70 02                      UTerm 2      imp
aa  72 01                      URef 1         ph
ac  30                         UTerm 0        al
ad  32                         URef 0           x
ae  72 01                      URef 1           ph
b0  00                         END
b1  00 .. (7 bytes)            padding to 0xb8

b8  01 00 00 00 00 00 00 81    bad.args[0]: bound, sort 1, deps {0}     {x: set}
c0  70 02                      UTerm 2      imp
c2  71 01                      UTermSave 1    p        -> heap[1] = (p x)
c4  32                         URef 0           x
c5  30                         UTerm 0        al
c6  32                         URef 0           x
c7  72 01                      URef 1           (p x)
c9  00                         END

ca  44 02                      Sort            (statement length 2)
cc  44 02                      Sort
ce  45 02                      Term
d0  45 02                      Term
d2  45 02                      Term
d4  42 0b                      Axiom           (length 11: next statement at 0xdf)
d6    52 01                      Ref 1         ph
d8    12                         Ref 0         x
d9    52 01                      Ref 1         ph
db    10                         Term 0        (al x ph)
dc    50 02                      Term 2        (imp ph (al x ph))
de    00                         END
df  46 10                      Thm             (length 16: next statement at 0xef)
e1    12                         Ref 0         x                     substitution for x
e2    12                         Ref 0         x
e3    51 01                      TermSave 1    (p x) -> heap[1]      substitution for ph
e5    52 01                      Ref 1         (p x)
e7    12                         Ref 0         x
e8    52 01                      Ref 1         (p x)
ea    10                         Term 0        (al x (p x))
eb    50 02                      Term 2        (imp (p x) (al x (p x)))   the claim
ed    14                         Thm 0         apply ax5
ee    00                         END
ef  00                         END of the proof stream
f0  00 00 00 00                read-ahead padding
```

This file decodes cleanly and its last proof is **rejected**, by `mm0-rs` and by mm0-c,
at the `Thm 0` step: `ph := (p x)` breaks the condition that `ph` does not depend on `x`.
Its sibling `bound_arg_vars.mmb` differs in three bytes (the binder of the predicate) and
is the subject of point 1 in the next section.

## 9. Where the sources differ

Every point found on which the formal semantics, mmb.md, `mm0-rs` and mm0-c do not say
the same thing. The rule for deciding is the one at the top of these notes: the formal
semantics first; where they are silent on a check, what mmb.md states (points 9, 10, 11
and 20, where `mm0-rs` is more lenient than its own format description); for the
layout, the framing and the index, `mm0-rs`; mm0-c is listed for comparison.

Each row marked with a fixture was checked by running both implementations on a
hand-assembled file from `tests/fixtures/disputed/` (`gen.py` there), `mm0-rs` as
`mm0-rs compile x.mmb` and mm0-c as `mm0-c x.mmb < x.mm0`. Points 8, 10, 11 and 20 have
fixtures among the files of `tests/fixtures/verify/` as well (`cases.tsv` names the
point). Rows without a fixture were checked on throwaway files in the same way, or on
the mutants in `tests/mmb/` of the MM0 repository.

| # | Point | Formal semantics | `mm0-rs` | mm0-c | We |
| - | ----- | ---------------- | -------- | ----- | -- |
| 1 | variables of a term whose argument is in a bound position (`bound_arg_vars`) | counted | counted: rejects | not counted: **accepts** | reject |
| 2 | which bound variables a regular argument must avoid | those it does not depend on | same | same | same; mmb.md's text is inverted |
| 3 | free variables of a bound argument, in a definition | none, except through the return type | same | same | same; mmb.md's text is wrong |
| 4 | `UDummy`: disjoint from what | the arguments | arguments, earlier dummies, finished saved terms | arguments, earlier dummies | arguments and earlier dummies |
| 5 | dummies of a `free` sort; free variables of a def's value | unclear: `mm0.md` and `mm0.mm0` differ | no such dummies; all free variables in `ret` | same as `mm0-rs` | as the implementations |
| 6 | `Sorry` (`sorry_expr`, `sorry_conv`) | no such rule | accepts the file | rejects | reject |
| 7 | `LocalDef` on an entry that is not a def (`local_term`) | not allowed | rejects | **accepts** | reject |
| 8 | the proof body of an `axiom` or `def` (`axiom_body_mismatch`) | checked (`mm0b.lean`) | **not read** | checked | check |
| 9 | sort in the term table vs sort of `ret` (`ret_sort_mismatch`) | — (mmb.md: must agree) | **not compared** | must agree | must agree |
| 10 | more than 55 bound variables | — (not representable) | **accepts** | rejects | reject |
| 11 | `deps` of a bound binder | — (mmb.md: exactly its own bit) | **ignored** | must be its own bit | must be its own bit |
| 12 | reserved fields, bit 55 of `arg` | — (mmb.md: zero) | not checked | not checked | not checked by the reader; reported by `dump` |
| 13 | 4 bytes of padding after the last `END` | — (mmb.md: required) | not required | required | not required to read; always written |
| 14 | a damaged index | — | **rejects** | ignores the index | reject, as section 7 |
| 15 | order and alignment of the sections | — | required, as section 2 | not checked | required |
| 16 | unknown bits in a sort's modifiers | — | rejects | only through the `.mm0` comparison | reject |
| 17 | the unify stream of a term or theorem | — (mmb.md: behind a pointer) | inline | inline | inline; mmb.md's table is wrong |
| 18 | equality of expressions | identity of nodes (`mm0b.lean`) | identity | identity | identity |
| 19 | fixed capacity limits | none | none | stack, heap, store, 256 hypotheses | none |
| 20 | fewer statements than table entries | — | **accepts** | rejects | reject |
| 21 | an `END` whose first byte has data-width bits (`0x40`, `0x80`, `0xC0`) | — (mmb.md: `END` is `0x00`) | accepts | rejects | accept |

What the implementations did with the fixtures (exit codes):

| Fixture | `mm0-rs` | mm0-c | Our verifier must |
| ------- | -------- | ----- | ----------------- |
| `bound_arg_vars` | 1 | 0 | reject |
| `regular_arg_vars` | 1 | 255 | reject |
| `sorry_expr` | 0 | 3 | reject |
| `sorry_conv` | 0 | 255 | reject |
| `local_term` | 1 | 0 | reject |
| `axiom_body_mismatch` | 0 | 255 | reject |
| `ret_sort_mismatch` | 0 | 255 | reject |

Notes on the points that need more than a table cell.

**1. Variables of a term in a theorem.** With `term foo {x: set}: wff x`, is `x` a
variable of `(foo x)`? `mm0.md` (`Vars(foo e1 ... en) = ⋃ Si`), `mm0.mm0` (`HasVarApp`),
`mm0.lean` (`sexpr.has_var`) and the `mm0-rs` kernel say yes: every argument counts.
mm0-c (`verifier.c`, the `Term` rule) adds nothing for an argument in a bound position,
so for it `(foo x)` has no variables. `bound_arg_vars` uses this to prove
`imp (foo x) (al x (foo x))` from `ax5 {x: set} (ph: wff): $ imp ph (al x ph) $` with
`ph := (foo x)`. The statement is not valid, since `foo x` is declared to depend on `x`,
and mm0-c accepts the proof. This is the reason mm0-c is not a reference.

**4. `UDummy`.** mmb.md says "disjoint from every element of the unify heap". Read
literally on the stack machine that cannot work: a `UTermSave` puts a term on the heap
before its arguments are read, so a saved term that contains the dummy is already there
when the dummy is reached. `mm0-rs` compares against the arguments, the earlier dummies
and the saved terms that are *finished*; mm0-c skips saved terms altogether. The two give
the same verdict: a finished saved term is built from arguments and earlier dummies, so
it adds nothing. `mm0.mm0` (`VerifyConvUnfold`) compares against the arguments only and,
as far as we can read it, does not ask the dummies of one unfolding to be distinct from
each other. Both implementations do, and without it `E. y E. z ~ y = z` could be unfolded
to `E. y E. y ~ y = y`, so we follow the implementations.

**5. `free` sorts.** This is the one point the formal semantics do not settle, because
its two parts disagree:

- `mm0.md`, on sorts: "`free` means that definitions and theorems are not allowed to use
  dummy variables with this sort";
- `mm0.md`, on definition checking: "every free variable in the definiens with a `free`
  sort is among the declared dependencies";
- `mm0.mm0` (`DefOk`): a free variable of the value must be among the declared
  dependencies *unless* its sort is `free`.

`mm0-rs` and mm0-c both do the strictest thing: no dummy may have a `free` sort, and
every free variable of a def's value must be among the dependencies of its return type.
Whatever they accept is accepted under each of the three readings, so following them is
safe. This choice among the readings was confirmed on 2026-10-01.

**6. `Sorry`.** `mm0-rs` treats a theorem whose proof contains `Sorry` as a theorem
without a proof, keeps it, and exits with 0. That is right for a compiler that may import
unfinished work and wrong for a verifier. mmb.md: verifiers "are required to report
failure for proofs using `Sorry`".

**8. Bodies of axioms and definitions.** `mm0-rs` takes the statement of an axiom and the
value of a definition from the unify stream in the table and never reads the proof body
that mmb.md asks to be checked against it. In `axiom_body_mismatch` the body builds `tru`
and the unify stream says `fls`. Checking the body is what mmb.md and `mm0b.lean`
describe, so we check it. (`mm0-rs` does not need the body to rule out cyclic terms; see
section 4.)

**10. More than 55 bound variables.** The `mm0-rs` kernel does report this, but as a
"non-fatal" error, and the `.mmb` importer drops non-fatal errors. The case is
`tests/mmb/fail/gi_dummy_reserved_bit.mmb` in the MM0 repository.

**18. Equality is identity.** A verifier that hash-conses treats structurally equal
terms as the same node and therefore accepts files that the format, `mm0b.lean` and both
implementations reject — for example one in which a `TermSave` was turned into a `Term`.
We use the model of the format: a node is its allocation index in a per-statement store.
That needs no hashing and is also the fastest. Hash-consing remains the right tool for
the prover. (The brief first listed hash-consing among the verifier's techniques; that
was changed on 2026-10-01.)

**20. Statements and table entries.** `mm0-rs` looks at a table entry only when a
statement declares it, and does not compare the number of statements with the header.
So it accepts a proof stream that stops early, and a header whose counts are too large
even if the extra table entries are garbage. Our reader reads every entry of the tables
and rejects an unreadable one; our verifier requires the counts to agree.

**21. `END` with a data width.** A byte `0x40` has opcode 0 and announces one byte of
data. As the last byte of a statement it is an `END` whose data byte would be the first
byte of the next statement. `mm0-rs` takes it as the `END` (it looks at the opcode and at
where the command starts), mm0-c computes a wrong statement length from it and rejects.
Nothing depends on the choice; the reference implementation is followed.

Noticed in passing, in the formal specification: in `VerifyProofThm` (`mm0.mm0`) and
`safe_subst` (`mm0.lean`) the test "`u` is a bound variable" looks `u` up in the *proof
context*, while `u` indexes the *theorem's* binders. It reads like a slip (it should be
the theorem's argument list), and both implementations use the theorem's binders. Worth
confirming before the verifier is modelled on it.

Differences in how the **`.mm0`** file is read are a separate list, in `DESIGN.md`.

## 10. The reader

`Whitehead/Mmb/Types.lean`, `Reader.lean`, `Encode.lean`, `Dump.lean`, and `Write.lean`, which writes a file with other proof bodies (`MmbFile.withBodies`, for `prove ... -o`): `END`, padding to a multiple of 8 and 8 zero bytes after each body, no index.

- Input: the whole file as one `ByteArray` (core Lean has no memory mapping).
- **`MmbFile.parse` opens a file.** It decodes the header, the sort table, the entries of
  the term and theorem tables, the index with its names, and the list of statements
  (kind, offsets of the statement and of its body, the table entry it declares). The
  statement list needs only the length fields, not the bodies.
- **Everything behind a table entry is read on demand**: the binders (`termArgs`,
  `thmArgs`, as `Arg` words with `sort`, `bound` and `deps` accessors), the unify streams
  (`termUnifyCmds`, `thmUnifyCmds`, or as trees: `termValue`, `thmStatement`) and the
  proof bodies (`proofCmds`). The first plan was to decode binders and unify streams when
  opening; the set.mm translation has 49,156 entries in its theorem table (axioms and
  theorems) and 6.6 MB of such data, which is
  not worth turning into heap objects for a verifier that reads them from the bytes.
  Opening `setmm.mmb` (39 MB) takes 8 ms; decoding every stream in it takes 0.35 s.
- `MmbFile.checkStreams` decodes every unify stream (as a tree) and every proof body once
  and reports the first error. Opening a file and running it is "the file decodes".
- Commands are decoded faithfully: `Term`/`TermSave` keep their `save` flag, the `data`
  width is not preserved (it carries no meaning), and an unknown opcode is an error at
  the offset where it occurs. `Encode.lean` is the inverse, in the shortest encoding;
  every stream of every file we have encodes back to its original bytes.
- The reader rejects what `mm0-rs` rejects when it opens and walks a file: a bad magic
  number or version, the layout rules of section 2, tables or data blocks that leave the
  file, unknown modifier bits in a sort, a damaged index (section 7), a statement whose
  framing is wrong (section 5), an unknown statement or command opcode, a unify stream
  that is not a well-formed pattern (section 4). It also decodes the proof bodies of
  axioms and definitions, which `mm0-rs` skips (section 9, point 8). Every error carries
  a file offset.
- The reader does not judge proofs. Everything in section 6, and points 1–11 and 20 of
  section 9, belong to the verifier.

On the mutated files of the MM0 repository (`tests/mmb/`): the reader rejects 14 and
decodes 7. The 14 are the files `mm0-rs` rejects while reading — with the same offsets
where it reports one — plus `unknown_op`, whose bad opcode sits in an axiom's body. The 7
that decode are wrong in ways only a verifier can see (`bad_return`, `disjoint`,
`gi_dummy_reserved_bit`, `one_bad_decl`, `pure_sort`, `unify_mismatch`, `uses_sorry`).

### `dump`

`mm0-whitehead dump file.mmb` prints every statement as the `.mm0` declaration it stands
for, formulas as s-expressions, and under it the proof commands with their file offsets:

```
theorem t (a: wff): $ dbl a $;
  0x16e: Ref 0  -- a
  0x16f: Term dbl
  0x171: Ref 0  -- a
  0x172: Ref 0  -- a
  0x173: Ref 0  -- a
  0x174: TermSave imp  -- heap[1]
  0x175: Thm ax1
  0x177: Conv
  0x178: Ref 1
  0x17a: Unfold
  0x17b: Refl
```

A `Ref` to a variable or hypothesis is annotated with its name; a command that adds to
the heap is annotated with the index it gets. Names come from the index, or are generated
as in section 7, with `d<k>` for the dummies of a proof and `?<j>` for what has no name
yet; a header line says the version and whether the file has an index. Non-zero
reserved fields and a term-table sort that differs from the return type are printed as
`-- note:` lines.
