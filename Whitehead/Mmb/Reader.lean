/-
The `.mmb` reader: `docs/MMB-NOTES.md` sections 1–5, 7 and 10.

`MmbFile.parse` opens a file: it decodes the header, the sort, term and theorem tables,
the index, and the list of statements of the proof stream, and rejects what `mm0-rs`
rejects when it opens a file. Binders, unify streams and proof bodies stay in the byte
array; the accessors below decode them on demand, and `MmbFile.checkStreams` decodes all
of them once to make sure they can be decoded.

Nothing here judges a proof: that is the verifier's work.
-/
import Whitehead.Mmb.Types

namespace Whitehead.Mmb

namespace Reader

def fail {α : Type} (pos : Nat) (msg : String) : Except MmbError α :=
  .error ⟨pos, msg⟩

/-! Little-endian reads. They do not check bounds: the caller has. -/

@[inline] def u8 (b : ByteArray) (p : Nat) : Nat :=
  (b.get! p).toNat

@[inline] def u16 (b : ByteArray) (p : Nat) : Nat :=
  u8 b p ||| (u8 b (p + 1) <<< 8)

@[inline] def u32 (b : ByteArray) (p : Nat) : Nat :=
  u16 b p ||| (u16 b (p + 2) <<< 16)

/-- A 64-bit word, kept as `UInt64` so that a set top bit does not make a big number. -/
def word64 (b : ByteArray) (p : Nat) : UInt64 :=
  (u32 b p).toUInt64 ||| ((u32 b (p + 4)).toUInt64 <<< 32)

/-- A 64-bit pointer or count. -/
def u64 (b : ByteArray) (p : Nat) : Nat :=
  (word64 b p).toNat

/-- The command at `pos`: its opcode (the low six bits), its data, and the position
after it. The top two bits of the first byte give the width of the data. -/
@[inline] def readCmd (b : ByteArray) (pos : Nat) : Except MmbError (Nat × Nat × Nat) :=
  if pos ≥ b.size then
    fail pos "a command is expected here, but the file ends"
  else
    let first := b.get! pos
    let op := (first &&& 0x3F).toNat
    let width := (first >>> 6).toNat
    if width == 0 then .ok (op, 0, pos + 1)
    else if width == 1 then
      if pos + 2 ≤ b.size then .ok (op, u8 b (pos + 1), pos + 2)
      else fail pos "this command is cut off by the end of the file"
    else if width == 2 then
      if pos + 3 ≤ b.size then .ok (op, u16 b (pos + 1), pos + 3)
      else fail pos "this command is cut off by the end of the file"
    else
      if pos + 5 ≤ b.size then .ok (op, u32 b (pos + 1), pos + 5)
      else fail pos "this command is cut off by the end of the file"

/-- The header, with the layout rules that `mm0-rs` checks (`Header::check`), and the
alignment it needs to read the tables in place. Errors point at the header field. -/
def readHeader (b : ByteArray) : Except MmbError Header := do
  if b.size < 40 then
    fail 0 s!"the file has {b.size} bytes, too few for the 40-byte header"
  if u32 b 0 != 0x42304D4D then
    fail 0 "bad magic number: an MMB file starts with `MM0B`"
  if u8 b 4 != 1 then
    fail 4 s!"MMB version {u8 b 4} is not supported; this reader knows version 1"
  let h : Header := {
    numSorts := u8 b 5, reserved := u16 b 6, numTerms := u32 b 8, numThms := u32 b 12,
    pTerms := u32 b 16, pThms := u32 b 20, pProof := u32 b 24, reserved2 := u32 b 28,
    pIndex := u64 b 32 }
  if 40 + h.numSorts > h.pTerms then
    fail 16 s!"p_terms = 0x{hex h.pTerms} lies inside the header or the sort table"
  if h.pTerms % 8 != 0 then
    fail 16 s!"p_terms = 0x{hex h.pTerms} must be a multiple of 8"
  if h.pTerms + 4 * h.numTerms > h.pThms then
    fail 20 s!"p_thms = 0x{hex h.pThms}: the theorem table must come after the term table"
  if h.pThms % 8 != 0 then
    fail 20 s!"p_thms = 0x{hex h.pThms} must be a multiple of 8"
  if h.pThms + 4 * h.numThms > h.pProof then
    fail 24 s!"p_proof = 0x{hex h.pProof}: the proof stream must come after the theorem table"
  if h.pProof > b.size then
    fail 24 s!"p_proof = 0x{hex h.pProof} is outside the file"
  if h.pIndex != 0 then
    if h.pIndex ≤ h.pProof || h.pIndex > b.size then
      fail 32 s!"p_index = 0x{hex h.pIndex}: the index must come after the proof stream, inside the file"
    if h.pIndex % 8 != 0 then
      fail 32 s!"p_index = 0x{hex h.pIndex} must be a multiple of 8"
  return h

def readSorts (b : ByteArray) (h : Header) : Except MmbError (Array SortData) := do
  let mut sorts := Array.mkEmpty h.numSorts
  for i in [0:h.numSorts] do
    let raw := b.get! (40 + i)
    if raw &&& 0xF0 != 0 then
      fail (40 + i) s!"sort {i} has unknown modifier bits: 0x{hex raw.toNat}"
    sorts := sorts.push ⟨raw⟩
  return sorts

def readTerms (b : ByteArray) (h : Header) : Except MmbError (Array TermEntry) := do
  if h.pTerms + 8 * h.numTerms > b.size then
    fail 16 s!"the term table ({h.numTerms} entries at 0x{hex h.pTerms}) runs past the end of the file"
  let mut terms := Array.mkEmpty h.numTerms
  for i in [0:h.numTerms] do
    let e := h.pTerms + 8 * i
    let numArgs := u16 b e
    let sortByte := u8 b (e + 2)
    let pData := u32 b (e + 4)
    if pData + 8 * (numArgs + 1) > b.size then
      fail e s!"the binders of term {i} ({numArgs} arguments at 0x{hex pData}) run past the end of the file"
    terms := terms.push {
      numArgs, sort := sortByte &&& 0x7F, isDef := sortByte &&& 0x80 != 0,
      reserved := u8 b (e + 3), pData }
  return terms

def readThms (b : ByteArray) (h : Header) : Except MmbError (Array ThmEntry) := do
  if h.pThms + 8 * h.numThms > b.size then
    fail 20 s!"the theorem table ({h.numThms} entries at 0x{hex h.pThms}) runs past the end of the file"
  let mut thms := Array.mkEmpty h.numThms
  for i in [0:h.numThms] do
    let e := h.pThms + 8 * i
    let numArgs := u16 b e
    let pData := u32 b (e + 4)
    if pData + 8 * numArgs > b.size then
      fail e s!"the binders of theorem {i} ({numArgs} arguments at 0x{hex pData}) run past the end of the file"
    thms := thms.push { numArgs, reserved := u16 b (e + 2), pData }
  return thms

/-- The statements of the proof stream from `pos` on. `nSorts`, `nTerms` and `nThms`
count the statements of each class seen so far. -/
partial def readStmts (b : ByteArray) (h : Header) (terms : Array TermEntry)
    (pos nSorts nTerms nThms : Nat) (acc : Array Stmt) : Except MmbError (Array Stmt) := do
  if pos ≥ b.size then
    fail pos "the proof stream reaches the end of the file without an END"
  let (op, data, next) ← readCmd b pos
  if op == 0 then
    return acc
  let stop := pos + data
  if stop < next then
    fail pos s!"the length of this statement ({data}) is smaller than the statement command itself"
  if stop > b.size then
    fail pos s!"this statement (length {data}) runs past the end of the file"
  if op == 0x04 then
    if nSorts ≥ h.numSorts then
      fail pos s!"more sort statements than the {h.numSorts} sorts of the header"
    if stop != next then
      fail pos "a sort statement has no proof body"
    readStmts b h terms stop (nSorts + 1) nTerms nThms (acc.push ⟨.sort, pos, next, stop, nSorts⟩)
  else if op == 0x05 || op == 0x0D then
    if nTerms ≥ h.numTerms then
      fail pos s!"more term and def statements than the {h.numTerms} entries of the term table"
    if !terms[nTerms]!.isDef && stop != next then
      fail pos s!"term {nTerms} is not a def and cannot have a proof body"
    readStmts b h terms stop nSorts (nTerms + 1) nThms
      (acc.push ⟨.termDef (op == 0x0D), pos, next, stop, nTerms⟩)
  else if op == 0x02 || op == 0x06 || op == 0x0E then
    if nThms ≥ h.numThms then
      fail pos s!"more axiom and theorem statements than the {h.numThms} entries of the theorem table"
    let kind := if op == 0x02 then StmtKind.ax else .thm (op == 0x0E)
    readStmts b h terms stop nSorts nTerms (nThms + 1) (acc.push ⟨kind, pos, next, stop, nThms⟩)
  else
    fail pos s!"unknown statement opcode 0x{hex op}"

/-! ### The index (section 7) -/

/-- The NUL-terminated UTF-8 string at `p`, if `p` is not null and leads to one. -/
def cstr (b : ByteArray) (p : Nat) : Option String :=
  if p == 0 || p ≥ b.size then none
  else
    let stop := Id.run do
      let mut q := p
      while q < b.size && b.get! q != 0 do
        q := q + 1
      return q
    if stop ≥ b.size then none else String.fromUTF8? (b.extract p stop)

/-- The string list at `p`: a count and that many string pointers. Empty if `p` is null
or the list does not fit in the file. -/
def strList (b : ByteArray) (p : Nat) : Array (Option String) :=
  if p == 0 || p + 8 > b.size then #[]
  else
    let n := u64 b p
    if n > (b.size - p - 8) / 8 then #[]
    else (Array.range n).map fun i => cstr b (u64 b (p + 8 + 8 * i))

/-- Is there a NUL at or after `p`? Returns the position after it. -/
def skipCstr (b : ByteArray) (p : Nat) : Option Nat := Id.run do
  let mut q := p
  while q < b.size do
    if b.get! q == 0 then return some (q + 1)
    q := q + 1
  return none

def readIndex (b : ByteArray) (h : Header) : Except MmbError (Array IndexEntry × Names) := do
  if h.pIndex == 0 then
    return (#[], {})
  let p := h.pIndex
  if p + 8 > b.size then
    fail 32 s!"p_index = 0x{hex p}: the index is cut off by the end of the file"
  let n := u64 b p
  if n > (b.size - p - 8) / 16 then
    fail p s!"the index claims {n} entries, more than fit in the file"
  let mut entries := Array.mkEmpty n
  let mut names : Names := {}
  let mut seen : Array String := #[]
  let nSorts := h.numSorts
  let nTerms := h.numTerms
  let nThms := h.numThms
  for i in [0:n] do
    let e := p + 8 + 16 * i
    let type := (String.fromUTF8? (b.extract e (e + 4))).getD s!"0x{hex (u32 b e)}"
    let ptr := u64 b (e + 8)
    entries := entries.push { type, data := u32 b (e + 4), ptr }
    if type == "Name" || type == "VarN" || type == "HypN" || type == "Delm" || type == "Nota" then
      if seen.contains type then
        fail e s!"the index table `{type}` occurs twice"
      seen := seen.push type
    let outside (what : String) : Except MmbError Unit :=
      fail e s!"the `{type}` table ({what} at 0x{hex ptr}) runs past the end of the file"
    if type == "Name" then
      let count := nSorts + nTerms + nThms
      if ptr % 8 != 0 then
        fail e s!"the `Name` table at 0x{hex ptr} must be at a multiple of 8"
      if ptr + 16 * count > b.size then outside s!"{count} entries"
      let name (k : Nat) := cstr b (u64 b (ptr + 16 * k + 8))
      names := { names with
        sorts := (Array.range nSorts).map name
        terms := (Array.range nTerms).map fun k => name (nSorts + k)
        thms := (Array.range nThms).map fun k => name (nSorts + nTerms + k) }
    else if type == "VarN" then
      if ptr + 8 * (nTerms + nThms) > b.size then outside s!"{nTerms + nThms} entries"
      let list (k : Nat) := strList b (u64 b (ptr + 8 * k))
      names := { names with
        termVars := (Array.range nTerms).map list
        thmVars := (Array.range nThms).map fun k => list (nTerms + k) }
    else if type == "HypN" then
      if ptr + 8 * nThms > b.size then outside s!"{nThms} entries"
      names := { names with thmHyps := (Array.range nThms).map fun k => strList b (u64 b (ptr + 8 * k)) }
    else if type == "Delm" then
      -- two NUL-terminated lists of delimiter bytes
      match skipCstr b ptr with
      | none => outside "the left delimiters"
      | some q => if (skipCstr b q).isNone then outside "the right delimiters"
    else if type == "Nota" then
      -- a pointer to the overflow area, which starts where the notation entries end
      if ptr + 8 > b.size then outside "its header"
      let overflow := u64 b ptr
      if overflow < ptr + 8 || overflow > b.size then
        fail e s!"the `Nota` table at 0x{hex ptr} has its overflow area at 0x{hex overflow}, outside the file or before the table"
  return (entries, names)

/-! ### Streams (sections 4 and 5) -/

/-- The proof commands in `[pos, stop)`. The last byte of the range must be the `END`. -/
partial def readProof (b : ByteArray) (pos stop : Nat) (acc : Array ProofCmd) :
    Except MmbError (Array ProofCmd) := do
  if pos ≥ stop then
    fail stop "the proof of this statement does not end with END"
  let (op, data, next) ← readCmd b pos
  if op == 0 then
    if pos + 1 == stop then return acc
    else fail pos "END before the end of the statement's proof"
  if next > stop then
    fail pos "the proof of this statement does not end with END: this command crosses its end"
  let cmd : ProofCmd ←
    match op with
    | 0x10 => pure (.term data false)
    | 0x11 => pure (.term data true)
    | 0x12 => pure (.ref data)
    | 0x13 =>
      if data > 255 then fail pos s!"Dummy: {data} is not a sort (a sort is one byte)"
      pure (.dummy data)
    | 0x14 => pure (.thm data false)
    | 0x15 => pure (.thm data true)
    | 0x16 => pure .hyp
    | 0x17 => pure .conv
    | 0x18 => pure .refl
    | 0x19 => pure .symm
    | 0x1A => pure .cong
    | 0x1B => pure .unfold
    | 0x1C => pure .convCut
    | 0x1E => pure .convSave
    | 0x1F => pure .save
    | 0x20 => pure .sorry
    | _ => fail pos s!"unknown proof command 0x{hex op}"
  readProof b next stop (acc.push cmd)

/-- The unify commands from `pos` up to the `END`, and the position after the `END`. -/
partial def readUnify (b : ByteArray) (pos : Nat) (acc : Array UnifyCmd) :
    Except MmbError (Array UnifyCmd × Nat) := do
  let (op, data, next) ← readCmd b pos
  if op == 0 then
    return (acc, next)
  let cmd : UnifyCmd ←
    match op with
    | 0x30 => pure (.term data false)
    | 0x31 => pure (.term data true)
    | 0x32 => pure (.ref data)
    | 0x33 =>
      if data > 255 then fail pos s!"UDummy: {data} is not a sort (a sort is one byte)"
      pure (.dummy data)
    | 0x36 => pure .hyp
    | _ => fail pos s!"unknown unify command 0x{hex op}"
  readUnify b next (acc.push cmd)

/-- The state of reading a unify stream as a tree. -/
structure PatternState where
  pos : Nat
  /-- One entry per heap index; `false` for a saved term whose arguments are still being
  read. A reference to such an entry would make a cyclic term. -/
  heap : Array Bool
  dummies : Array Nat

/-- One pattern of a unify stream, starting at `st.pos`. -/
partial def readPattern (b : ByteArray) (terms : Array TermEntry) (isDef : Bool)
    (st : PatternState) : Except MmbError (Pattern × PatternState) := do
  let pos := st.pos
  let (op, data, next) ← readCmd b pos
  if op == 0x30 || op == 0x31 then
    let some t := terms[data]?
      | fail pos s!"this unify command names term {data}, but the file has {terms.size} terms"
    let save := op == 0x31
    let slot := st.heap.size
    let mut st : PatternState :=
      { st with pos := next, heap := if save then st.heap.push false else st.heap }
    let mut args := Array.mkEmpty t.numArgs
    for _ in [0:t.numArgs] do
      let (arg, st') ← readPattern b terms isDef st
      args := args.push arg
      st := st'
    if save then
      st := { st with heap := st.heap.set! slot true }
    return (.app data (if save then some slot else none) args, st)
  else if op == 0x32 then
    match st.heap[data]? with
    | some true => return (.ref data, { st with pos := next })
    | some false =>
      fail pos s!"cyclic reference: heap entry {data} is a term that is still being read"
    | none =>
      fail pos s!"reference to heap entry {data}, but the unify heap has {st.heap.size} entries here"
  else if op == 0x33 then
    if !isDef then
      fail pos "UDummy is only allowed in the unify stream of a def"
    if data > 255 then
      fail pos s!"UDummy: {data} is not a sort (a sort is one byte)"
    return (.dummy data st.heap.size,
      { pos := next, heap := st.heap.push true, dummies := st.dummies.push data })
  else if op == 0x36 then
    fail pos "UHyp inside a pattern"
  else if op == 0 then
    fail pos "the unify stream ends inside a pattern"
  else
    fail pos s!"unknown unify command 0x{hex op}"

/-- The hypotheses that follow the conclusion: `UHyp <pattern>` repeated, then `END`. -/
partial def readHyps (b : ByteArray) (terms : Array TermEntry) (st : PatternState)
    (acc : Array Pattern) : Except MmbError (Array Pattern × PatternState) := do
  let (op, _, next) ← readCmd b st.pos
  if op == 0 then
    return (acc, { st with pos := next })
  else if op == 0x36 then
    let (hyp, st) ← readPattern b terms false { st with pos := next }
    readHyps b terms st (acc.push hyp)
  else
    fail st.pos "expected UHyp or END after a complete pattern"

/-- A whole unify stream as a tree: one pattern for a def; a conclusion and hypotheses
for an axiom or theorem. The stream stores the hypotheses last to first; they are
returned in declaration order. -/
def readStatement (b : ByteArray) (terms : Array TermEntry) (isDef : Bool) (numArgs pos : Nat) :
    Except MmbError Statement := do
  let (concl, st) ← readPattern b terms isDef ⟨pos, Array.replicate numArgs true, #[]⟩
  if isDef then
    let (op, _, _) ← readCmd b st.pos
    if op != 0 then
      fail st.pos "the unify stream of a def is one pattern: expected END"
    return ⟨concl, #[], st.dummies⟩
  else
    let (hyps, st) ← readHyps b terms st #[]
    return ⟨concl, hyps.reverse, st.dummies⟩

end Reader

open Reader

namespace MmbFile

/-- Opens a file: header, tables, index and the statement list. -/
def parse (bytes : ByteArray) : Except MmbError MmbFile := do
  let header ← readHeader bytes
  let sorts ← readSorts bytes header
  let terms ← readTerms bytes header
  let thms ← readThms bytes header
  let (indexEntries, names) ← readIndex bytes header
  let stmts ← readStmts bytes header terms header.pProof 0 0 0 #[]
  return { bytes, header, sorts, terms, thms, stmts, indexEntries, names }

/-- The binders of term `i`. -/
def termArgs (f : MmbFile) (i : Nat) : Array Arg :=
  let t := f.terms[i]!
  (Array.range t.numArgs).map fun k => ⟨word64 f.bytes (t.pData + 8 * k)⟩

/-- The return type of term `i`. -/
def termRet (f : MmbFile) (i : Nat) : Arg :=
  let t := f.terms[i]!
  ⟨word64 f.bytes (t.pData + 8 * t.numArgs)⟩

/-- Where the unify stream of term `i` starts, if it is a def. -/
def termUnifyPos (f : MmbFile) (i : Nat) : Nat :=
  let t := f.terms[i]!
  t.pData + 8 * (t.numArgs + 1)

/-- The binders of theorem `i`. -/
def thmArgs (f : MmbFile) (i : Nat) : Array Arg :=
  let t := f.thms[i]!
  (Array.range t.numArgs).map fun k => ⟨word64 f.bytes (t.pData + 8 * k)⟩

/-- Where the unify stream of theorem `i` starts. -/
def thmUnifyPos (f : MmbFile) (i : Nat) : Nat :=
  let t := f.thms[i]!
  t.pData + 8 * t.numArgs

/-- The unify commands of term `i`; none if it is not a def. -/
def termUnifyCmds (f : MmbFile) (i : Nat) : Except MmbError (Array UnifyCmd) :=
  if f.terms[i]!.isDef then (readUnify f.bytes (f.termUnifyPos i) #[]).map (·.1) else .ok #[]

/-- The unify commands of theorem `i`. -/
def thmUnifyCmds (f : MmbFile) (i : Nat) : Except MmbError (Array UnifyCmd) :=
  (readUnify f.bytes (f.thmUnifyPos i) #[]).map (·.1)

/-- The value of def `i`, as a tree. -/
def termValue (f : MmbFile) (i : Nat) : Except MmbError Statement :=
  readStatement f.bytes f.terms true f.terms[i]!.numArgs (f.termUnifyPos i)

/-- The conclusion and hypotheses of theorem `i`, as trees. -/
def thmStatement (f : MmbFile) (i : Nat) : Except MmbError Statement :=
  readStatement f.bytes f.terms false f.thms[i]!.numArgs (f.thmUnifyPos i)

/-- Does this statement have a proof body: an axiom, a theorem or a def? -/
def hasBody (f : MmbFile) (s : Stmt) : Bool :=
  match s.kind with
  | .sort => false
  | .termDef _ => f.terms[s.index]!.isDef
  | .ax | .thm _ => true

/-- The proof commands of a statement, without the final `END`; none for a sort or a
term. -/
def proofCmds (f : MmbFile) (s : Stmt) : Except MmbError (Array ProofCmd) :=
  if f.hasBody s then readProof f.bytes s.bodyStart s.stop #[] else .ok #[]

/-- Decodes every unify stream and every proof body, and returns the first error. -/
def checkStreams (f : MmbFile) : Except MmbError Unit := do
  for i in [0:f.terms.size] do
    if f.terms[i]!.isDef then
      discard <| f.termValue i
  for i in [0:f.thms.size] do
    discard <| f.thmStatement i
  for s in f.stmts do
    discard <| f.proofCmds s

/-! Names, from the index or generated (section 7). -/

def sortName (f : MmbFile) (i : Nat) : String :=
  (f.names.sorts[i]?.join).getD s!"s{i}"

def termName (f : MmbFile) (i : Nat) : String :=
  (f.names.terms[i]?.join).getD s!"t{i}"

def thmName (f : MmbFile) (i : Nat) : String :=
  (f.names.thms[i]?.join).getD s!"T{i}"

/-- `count` names: the stored ones where there are any, `<prefix><index>` otherwise. If
more names are stored than `count`, all of them are returned. -/
def fillNames (stored : Array (Option String)) (count : Nat) (pre : String) : Array String :=
  (Array.range (max count stored.size)).map fun i => (stored[i]?.join).getD s!"{pre}{i}"

/-- The names of the variables of term `i`: its arguments, then the dummies the index
knows about. -/
def termVarNames (f : MmbFile) (i : Nat) : Array String :=
  fillNames (f.names.termVars[i]?.getD #[]) f.terms[i]!.numArgs "v"

/-- The names of the variables of theorem `i`: its arguments, then the dummies the index
knows about. -/
def thmVarNames (f : MmbFile) (i : Nat) : Array String :=
  fillNames (f.names.thmVars[i]?.getD #[]) f.thms[i]!.numArgs "v"

/-- The names of the hypotheses of theorem `i`. Their number comes from its unify
stream. -/
def thmHypNames (f : MmbFile) (i : Nat) : Array String :=
  let count := match f.thmStatement i with
    | .ok s => s.hyps.size
    | .error _ => 0
  fillNames (f.names.thmHyps[i]?.getD #[]) count "h"

end MmbFile

end Whitehead.Mmb
