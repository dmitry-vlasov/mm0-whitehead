# The `.mmb` format — our notes

This is our own description of the MMB binary proof format, written from the spec and
from reading the reference verifier. It is meant to be enough to re-implement the reader
without opening either. Where the spec and the reference verifier disagree, both are
recorded and the point is listed under [Disagreements and open questions](#9-disagreements-and-open-questions);
none of them has been resolved by guessing.

Sources, all in the local checkout `/home/dmitry/tools/mm0` at commit `0d414c0b`:

| Short name | File | Role |
| ---------- | ---- | ---- |
| **spec** | `mm0-c/mmb.md` | the written format description |
| **mm0-c** | `mm0-c/{types,verifier_types,verifier,parser,index}.c` | the reference verifier; our oracle |
| mm0.md | `mm0.md` | the `.mm0` language and the informal semantics |
| mm0.mm0 | `examples/mm0.mm0` | the formal specification of MM0, written in MM0 |
| mm0.lean | `mm0-lean/mm0/mm0.lean`, `mm0b.lean` | the Lean 3 formalization (semantics; MMB machine) |
| mm0-rs | `mm0-rs/src/mmb/export.rs`, `mm0-rs/src/elab/verify.rs` | the writer of every `.mmb` we have; a second kernel |
| mm0-js | `mm0-js/src/machine.ts` | a third verifier, a port of mm0-c |

Everything in sections 1–7 was checked by decoding real files with a throwaway script
written from these notes alone: `mm0-js/test/hol.mmb`, `mm0-js/test/peano.mmb`,
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

A file is a header followed by sections reached through pointers. The format fixes only
the header position; the order below is what `mm0-rs` writes and what every file we have
looks like.

```
0x00  header (40 bytes)
0x28  sort table            num_sorts bytes, then zero padding to a multiple of 8
      term table            num_terms entries of 8 bytes          <- p_terms
      theorem table         num_thms entries of 8 bytes           <- p_thms
      term data, thm data   one 8-aligned block per entry          <- each entry's p_data
      proof stream          byte-aligned, ends with END           <- p_proof
      index payload         names, variable names, ...
      index                 the index header itself comes last     <- p_index
```

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
| 4–7 | | unused, `0` |

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

Note that `unify` is not a pointer: the spec's table says `p32<unify_stream>`, but the
stream is stored inline, immediately after `ret` (mm0-c reads it at `&args[num_args+1]`,
and so do the real files).

### Theorem table

`num_thms` entries of 8 bytes at `p_thms`:

| Offset | Size | Field | Meaning |
| ------ | ---- | ----- | ------- |
| 0 | 2 | `num_args` | number of expression arguments (variables, not hypotheses) |
| 2 | 2 | `reserved` | `0` |
| 4 | 4 | `p_data` | `p32` to the theorem data |

Theorem data at `p_data`: `8 * num_args` bytes of `arg` words, then a unify stream
inline (again not a pointer, whatever the spec's table says). There is no return type and
**no hypothesis count**: the number of hypotheses is the number of `UHyp` commands in the
unify stream.

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
shortest; a reader must accept all.

**Read-ahead rule.** mm0-c refuses to decode a command unless 5 bytes are readable at
its position, whatever its actual size (`cmd + 5 <= end of file`). So the last command
of the file must be followed by at least 4 more bytes. A file without an index therefore
ends with 4 bytes of padding after the final `END`.

In the low bit of the opcodes that come in pairs (`0x10/0x11`, `0x14/0x15`,
`0x30/0x31`), `1` means "and save".

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
recover the tree (and the hypothesis count) from the stream and the term table.

`UTermSave` records the term *before* its arguments are read, so a stream can describe a
cyclic term (`UTermSave 0, URef <itself>`). Such files are invalid; the verifier rules
them out by checking a def's unify stream against the value its proof stream builds.

## 5. Proof stream

The proof stream at `p_proof` has two levels: a sequence of **statements**, each of which
may contain a sequence of **proof commands**.

### Statements

A statement is a command whose `data` is the distance in bytes from the start of this
statement to the start of the next one. The stream ends at a byte equal to `0x00`.

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

Framing, as mm0-c checks it:

- a statement without a body has `data` equal to its own encoded size;
- a statement with a body is followed directly by proof commands up to and including an
  `END`, and `data` must point exactly past that `END`;
- the next statement position must again satisfy the read-ahead rule.

Whether `0x05` is a `term` or a `def` is decided by the def bit of the table entry, not
by the opcode. (Consequence: `0x0D` on an entry without the def bit is a term that has no
`.mm0` counterpart — see D8.)

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
| `0x20` | `Sorry` | 0 | admit a goal; never valid (see D6) |

Opcode `0x1D` is unassigned. Proofs are in **postfix** order: arguments first, then the
constructor.

Opcodes seen in the well-formed files we have: all of the above except `Sorry`; `data`
widths 0, 1 and 2 bytes.

## 6. What the commands mean

The reader only decodes; this section is what the `dump` output has to be understood
against, and it is the starting point for phase 2. It describes **mm0-c's behaviour**,
line references to `mm0-c/verifier.c`.

### Machine state

- **store** — the expression nodes built so far in the current statement. Two nodes are
  *the same expression* only if they are the same node: equality is identity, never
  structural comparison. `Term 0, Term 0` builds two different nodes.
- **stack** `S` — elements are one of: `expr e`; `proof e` (written `⊢ e`); a conversion
  `e1 = e2`; an obligation `e1 =?= e2`.
- **heap** `H` — `expr`, `proof` or conversion elements, addressed by index.
- **hyps** `HS` — the hypotheses declared so far (theorems only).
- **next_bv** — how many bound variables exist; the next dummy gets this bit.

Each node carries a sort, a `bound` flag (true only for bound variables and dummies), and
a 55-bit set `deps(e)`.

At the start of every statement the store, stack and hyps are emptied and the heap is
loaded with one variable node per argument (`load_args`, l.178), checking the `arg`
rules of section 2 against the sorts declared **so far**, and that no bound variable has
a `strict` sort.

### Proof commands (l.341–663)

`Term t` / `TermSave t` — `t` must be less than the number of terms declared so far (no
forward or self reference). Pop `num_args` elements, all of which must be `expr`. For
argument `i` with binder `a_i`: the sorts must be equal, and if `a_i` is bound then the
argument must be a bound variable. The new node has the term's result sort,
`bound = false`, and

```
deps(t e1 ... en) =   union over the REGULAR arguments i of  D_i
                    ∪ (definitions only) union of deps(e_j) for the bound arguments j
                                         that the return type depends on
D_i = deps(e_i)                                              in a theorem or axiom
D_i = deps(e_i) minus deps(e_j) for each bound argument j    in a definition
      that a_i is declared to depend on
```

A bound argument contributes nothing by itself in either mode (l.446–454; see D1).

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
`END` — stop; the caller checks the result.

Nothing in mm0-c forbids the conversion commands in a definition, but they cannot fire
there: every one needs a `⊢` or an obligation, and a definition's stack and heap only
ever hold `expr`.

### Unify commands (`run_unify`, l.213–331)

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
  `deps` must be disjoint from every heap entry that is **not** marked saved (the
  arguments and the earlier dummies); append it to the heap.
- `UHyp` — in `UThm`: pop `⊢ e` from the **main** stack, push `e`. In `UThmEnd`: the
  unify stack must be empty; pop the most recent entry of `HS`, push it. In `UDef`: error.
- `END` — the unify stack must be empty; in `UThmEnd` the hyps must also be used up.

### End of a statement (`verify`, l.670–819)

- `Sort`: the counter must be below `num_sorts`.
- `Term`/`Def`/`LocalDef`: result sort declared and not `pure`; `ret` checked like an
  argument and its sort field must equal the table's sort. For a def: run the body; the
  stack must hold exactly one `expr e`; `sort(e)` must equal the result sort; `deps(e)`
  must be a subset of `ret.deps`; then unify in mode `UDef` against the def's own stream.
- `Axiom`/`Thm`/`LocalThm`: run the body; the stack must hold exactly one element, an
  `expr e` for an axiom and a `⊢ e` for a theorem; `sort(e)` must be `provable`; then
  unify in mode `UThmEnd`.
- After the last statement: the three counters must match the header, no proof may have
  used `Sorry`, and the `.mm0` input must be at its end.

Non-local statements are matched against the next `.mm0` statement of the same kind
before the counter is incremented; that matching (`parser.c`) is phase-2 material and is
not described here.

## 7. The index

The index is optional and advisory: it holds names and notation, and nothing in it
affects verification. mm0-c reads it only to print error messages.

At `p_index`: a `u64` count `num_entries`, then that many 16-byte entries.

| Offset | Size | Field |
| ------ | ---- | ----- |
| 0 | 4 | `type` — four ASCII bytes |
| 4 | 4 | `data` — depends on the type |
| 8 | 8 | `ptr` — `p64` to the table |

Unknown types must be skipped. The tables we will read:

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

The other defined types are `"Delm"` (delimiters), `"Nota"` (notations), `"Lisp"` and
`"Deps"` (both `mm0-rs` extensions). They are specified in the spec; we do not need them
for phase 1 and the reader will keep their entries as raw `(type, data, ptr)` triples.
`"Delm"` and `"Nota"` would let `dump` print expressions in notation; that is a possible
later addition, not a planned one.

`tests/mmb/fail-index/` in the MM0 repository holds files with a broken index that mm0-c
accepts. Our reader must treat a damaged index as "no names available", not as a
decoding failure of the file.

## 8. A complete small file

`tests/fixtures/questions/regular_arg_vars.mmb` (244 bytes), for the specification

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

This file decodes cleanly and is **rejected** by mm0-c at the `Thm 0` step ("disjoint
variable violation"): `ph := (p x)` breaks the condition that `ph` does not depend on
`x`. Its sibling
`bound_arg_vars.mmb` differs in three bytes (the binder of the predicate) and is the
subject of D1.

## 9. Disagreements and open questions

The brief says to stop and ask when the spec and mm0-c disagree. These are all the
disagreements found in the `.mmb` format and its checking. Each has a proposal; **none
is decided**. D1 is the one with consequences; D2–D9 are places where the spec text is
wrong or silent and mm0-c is the better guide.

The fixtures named below are in `tests/fixtures/questions/`, hand-assembled by `gen.py`
there. What mm0-c (built from the checkout above, `gcc main.c -O2`) does with them:

| Fixture | mm0-c exit code | Message |
| ------- | --------------- | ------- |
| `bound_arg_vars` | 0 | accepted |
| `regular_arg_vars` | 255 | disjoint variable violation |
| `sorry_expr` | 3 | some theorems used sorry |
| `sorry_conv` | 255 | bad stack slot |
| `local_term` | 0 | accepted |

### D1. Which variables does a term have in a theorem? (mm0-c accepts an unsound proof)

- Spec: `V(t e1 ... en) = V(e1) ∪ ... ∪ V(en)`, all arguments. mm0.md says the same
  (`Vars(foo e1 ... en) = ⋃ Si`), and so do mm0.mm0 (`HasVarApp`), mm0.lean
  (`sexpr.has_var`) and the `mm0-rs` kernel (`verify.rs`, `accum |=` for every argument).
- mm0-c (`verifier.c` l.446–454) adds nothing for an argument in a **bound** position,
  in theorems as well as in definitions. mm0-js copies this.
- It matters when a bound variable reaches the result only through the return type:
  with `term foo {x: set}: wff x`, mm0-c computes that `(foo x)` has no variables.
- Evidence: `tests/fixtures/questions/bound_arg_vars.{mm0,mmb}` proves
  `imp (foo x) (al x (foo x))` from `ax5 {x: set} (ph: wff): $ imp ph (al x ph) $` by
  taking `ph := (foo x)`. **mm0-c accepts it** (exit code 0, with and without the
  `.mm0` check). The formal semantics reject it, and they are right to: `foo x` is
  declared to depend on `x`. The control `regular_arg_vars` is rejected by mm0-c.
- This puts two lines of the brief in conflict: "structurally close to the MM0 semantics
  formalization" and "any case where we accept and mm0-c rejects (or vice versa) is a
  bug".
- Proposal: follow the formal semantics (reject), and record this as the one known,
  documented deviation from the oracle, with the fixture as its regression test. It may
  also be worth reporting upstream.

### D2. The disjointness condition in the spec's `Thm` rule is inverted

- Spec: "For each `j` such that `thm[T].args[i].deps[j]`: check that
  `deps[j] ∩ FV(ei) = {}`" — i.e. for the bound variables the argument *does* depend on.
- mm0-c (l.505–507) checks the bound variables the argument does **not** depend on.
  mm0.md, mm0.mm0 and mm0.lean agree with mm0-c.
- Proposal: follow mm0-c; the spec text is a slip.

### D3. Free variables of a bound argument, in a definition

- Spec: "if `term[t].args[i].bound`, `Si = FV(ei)`" — a bound argument contributes its
  variable to the free variables of the term.
- mm0-c: a bound argument contributes nothing; it comes back only through the return
  type. mm0.md ("`FV(A. x ...) = FV(...) \ {x}`") and mm0.mm0 (`FreeApp`) agree with
  mm0-c. With the spec's reading no quantifier would bind anything.
- Proposal: follow mm0-c.

### D4. `UDummy`: disjoint from which heap entries?

- Spec: "`V(e) ∩ V(x) = {}` for all `e` in `H`".
- mm0-c (l.284–288): only the entries not created by `UTermSave`. A saved term contains
  the dummies that occur inside it, so the spec's reading would reject every definition
  that saves a subterm containing a dummy. (mm0.mm0, `VerifyConvUnfold`, compares against
  the arguments only and, as far as we can read it, does not ask the dummies to be
  distinct from each other; mm0-c does.)
- Proposal: follow mm0-c.

### D5. `Dummy` and `free` sorts; what a definition may leave free

- Spec: `Dummy s` requires `!sort[s].strict`. mm0-c also requires `!free` (l.399). mm0.md
  agrees with mm0-c ("`free` means that definitions and theorems are not allowed to use
  dummy variables with this sort").
- Related: for the end-of-def check mm0-c requires **every** free variable of the value
  to be among the return type's dependencies. mm0.mm0 (`DefOk`) exempts variables whose
  sort is `free`; mm0.md's "Definition checking" section constrains only variables of a
  `free` sort. These three do not say the same thing; mm0-c is the strictest and implies
  the other two.
- Proposal: follow mm0-c on both.

### D6. `Sorry`

- Spec: pops an `expr e` and pushes `⊢ e`, or pops an obligation `e1 =?= e2`.
- mm0-c (l.638–649): the second case requires a conversion `e1 = e2` on top, not an
  obligation, so `Sorry` on an obligation fails with "bad stack slot". It is also
  rejected in definitions. A file that uses `Sorry` is rejected either way.
- Evidence: `sorry_expr.mmb` exits with code 3 ("some theorems used sorry");
  `sorry_conv.mmb` exits with 255 ("bad stack slot").
- Proposal: decode `0x20` as `Sorry`; the verifier rejects any proof that contains it, as
  the spec allows ("verifiers are permitted to not recognize its existence").

### D7. Things mm0-c does not check

- The reserved fields (`reserved`, `reserved2`, the term and theorem table padding) and
  bit 55 of an `arg` word are not checked to be zero, except that a non-local statement's
  binders are compared with the `.mm0` binders, which catches bit 55 on regular variables.
- The alignment of `p_terms`, `p_thms` and `p_data` is not checked.
- `END` inside a stream is recognized by its low six bits, so `0x40 nn` also ends a
  stream; the END of the whole proof stream must be the exact byte `0x00`.
- The index is never validated.
- Proposal: the **reader** accepts all of these and reports the non-zero reserved fields
  and misaligned pointers in `dump` as warnings. Whether the **verifier** should reject
  them is a phase-2 question (it would make us stricter than the oracle on mutated
  files).

### D8. A local term

- A `LocalDef` statement (`0x0D`) whose table entry has no def bit is accepted by mm0-c
  as a term constructor with no `.mm0` counterpart. The spec's statement table does not
  mention this case. A new uninterpreted term is harmless, but it is not a definition.
- Evidence: `local_term.mmb` declares a term `hidden` this way; mm0-c accepts it against
  a `.mm0` file that never mentions `hidden`.
- Proposal: decode it as "local term" and accept it, as mm0-c does.

### D9. The unify stream is inline, not behind a pointer

- Spec: the `unify` field of `term_data` and `thm_data` has type `p32<unify_stream>`.
- mm0-c reads the stream itself at that position (`&args[num_args + 1]` for a def,
  `&args[num_args]` for a theorem), and so do all the files we have.
- Proposal: follow mm0-c; the type in the spec's table is a slip.

Differences between `mm0.md` and mm0-c's parser of the **`.mm0`** file are a separate
list, in `DESIGN.md`.

### Questions for phase 2 (no answer needed to write the reader)

- **Q1. Identity or structural equality?** mm0-c compares expressions by node identity,
  and the spec insists on it (`Term 0, Term 0` builds two different terms). The brief
  suggests hash-consing as the place for performance work. A hash-consing verifier
  accepts strictly more files than mm0-c — for example a mutant in which a `TermSave` was
  turned into a `Term` — which the differential test would count as a bug. Proposal: use
  mm0-c's model (a node is its allocation index in a per-statement store; no hashing,
  which is also the fastest), and keep hash-consing for the prover.
- **Q2. mm0-c's fixed limits.** Stack and heap 65536 entries, store 64 MB, 256
  hypotheses, unify stack 256. Files beyond them are rejected by mm0-c for capacity, not
  for being wrong. Proposal: no fixed limits on our side; the differential test
  classifies "mm0-c ran out of room" separately.
- **Q3. Noticed in passing, in the formalization.** In `VerifyProofThm` (mm0.mm0) and
  `safe_subst` (mm0.lean) the test "`u` is a bound variable" looks up the *proof context*
  `ctx`, while `u` indexes the *theorem's* binders. It reads like a slip (it should be the
  theorem's argument list). Worth confirming before the verifier is modelled on it.

## 10. The reader we intend to write

For review before any of it is written.

- Input: the whole file as one `ByteArray` (core Lean has no memory mapping).
- **Decoded eagerly**: header, sort table, term table and theorem table with their
  binders as structured values (`sort`, `bound`, `deps`), every unify stream as an
  `Array UnifyCmd`, the statement list (kind, byte range of the body, the table index it
  consumes), and the `Name`/`VarN`/`HypN` index tables.
- **Proof bodies are decoded on demand.** The reader gives a function that decodes one
  statement's body into an `Array ProofCmd`, and a non-allocating step function
  `(bytes, pos) -> (opcode, data, next pos)`. `dump` uses the first. The verifier will
  use the second: `peano.mmb` alone has 250,000 proof commands in under a megabyte, the
  set.mm translation will be far larger, and one heap object per command is a cost the
  phase-2 time budget cannot afford.
- Commands are decoded faithfully: `Term`/`TermSave` stay distinct constructors' worth of
  information (a `save` flag), the `data` width is not preserved (it carries no meaning),
  and an unknown opcode is an error at the offset where it occurs.
- Every read is bounds-checked and every error carries a file offset. The 5-byte
  read-ahead rule is enforced as mm0-c enforces it, so that we agree with it on truncated
  files.
- A missing or damaged index never fails the read (section 7).
