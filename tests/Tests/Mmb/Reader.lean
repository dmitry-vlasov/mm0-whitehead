/-
Tests for the `.mmb` reader.

The positive tests decode `tests/fixtures/disputed/regular_arg_vars.mmb`, the file that
`docs/MMB-NOTES.md` section 8 annotates byte by byte, and `tests/fixtures/mmb/small.mmb`,
which has an index. The negative tests corrupt single bytes of the first file; the
offsets in them are the offsets of that annotated listing.
-/
import Whitehead.Mmb.Reader
import Whitehead.Mmb.Encode
import Whitehead.Mmb.Dump
import Tests.Harness

open Whitehead.Mmb

namespace Tests.Mmb

def annotated : System.FilePath := "tests/fixtures/disputed/regular_arg_vars.mmb"
def small : System.FilePath := "tests/fixtures/mmb/small.mmb"
def smallDump : System.FilePath := "tests/fixtures/mmb/small.dump"

instance : ToString MmbError := ⟨fun e => s!"0x{String.ofList (Nat.toDigits 16 e.pos)}: {e.msg}"⟩
instance : ToString ProofCmd := ⟨fun c => toString (repr c)⟩
instance : ToString UnifyCmd := ⟨fun c => toString (repr c)⟩
instance : ToString Pattern := ⟨fun p => toString (repr p)⟩
instance : ToString StmtKind := ⟨fun k => toString (repr k)⟩
instance {α : Type} [BEq α] : BEq (Except MmbError α) := ⟨fun
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false⟩

/-- `bytes` with the byte at each given offset replaced. -/
def patch (bytes : ByteArray) (edits : List (Nat × UInt8)) : ByteArray :=
  edits.foldl (fun b (pos, v) => b.set! pos v) bytes

/-- Opening `bytes` and decoding every stream succeeds. -/
def fullyDecodes (bytes : ByteArray) : Except MmbError MmbFile := do
  let file ← MmbFile.parse bytes
  file.checkStreams
  return file

/-- The corrupted file is rejected at offset `pos` with a message containing `part`. -/
def rejectsAt (name : String) (bytes : ByteArray) (edits : List (Nat × UInt8)) (pos : Nat)
    (part : String) : TestM Unit := do
  match fullyDecodes (patch bytes edits) with
  | .ok _ => check name false "accepted"
  | .error e =>
    check name (e.pos == pos && contains e.msg part)
      s!"expected an error at 0x{String.ofList (Nat.toDigits 16 pos)} containing \"{part}\"\n  actual:   {e}"

def annotatedTests (bytes : ByteArray) : TestM Unit := do
  let file ←
    match fullyDecodes bytes with
    | .ok f => pure f
    | .error e => check "mmb: the annotated file decodes" false (toString e); return
  let h := file.header
  checkEq "mmb: header counts" (h.numSorts, h.numTerms, h.numThms) (2, 3, 2)
  checkEq "mmb: header pointers" (h.pTerms, h.pThms, h.pProof, h.pIndex) (0x30, 0x48, 0xca, 0)
  checkEq "mmb: sort modifiers" (file.sorts.toList.map fun s => (s.isPure, s.isStrict, s.isProvable, s.isFree))
    [(false, false, true, false), (false, false, false, false)]
  -- term 0: al {x: set} (ph: wff x): wff
  let al := file.terms[0]!
  checkEq "mmb: term entry" (al.numArgs, al.sort, al.isDef, al.pData) (2, 0, false, 0x58)
  checkEq "mmb: term binders" ((file.termArgs 0).toList.map fun a => (a.bound, a.sort, a.deps))
    [(true, 1, 1), (false, 0, 1)]
  let ret := file.termRet 0
  checkEq "mmb: term return type" (ret.bound, ret.sort, ret.deps) (false, 0, 0)
  checkEq "mmb: binder of a regular argument" ((file.termArgs 1).toList.map fun a => (a.bound, a.sort, a.deps))
    [(false, 1, 0)]
  -- theorems and their unify streams
  checkEq "mmb: theorem entries" (file.thms.toList.map fun t => (t.numArgs, t.pData)) [(2, 0x98), (1, 0xb8)]
  checkEq "mmb: unify stream of ax5" (file.thmUnifyCmds 0)
    (.ok #[.term 2 false, .ref 1, .term 0 false, .ref 0, .ref 1])
  checkEq "mmb: unify stream of bad" (file.thmUnifyCmds 1)
    (.ok #[.term 2 false, .term 1 true, .ref 0, .term 0 false, .ref 0, .ref 1])
  -- the statement of `bad`: imp (p x) (al x (p x)), the second (p x) being a back-reference
  checkEq "mmb: statement of bad as a pattern" ((file.thmStatement 1).map fun s => (s.concl, s.hyps.size))
    (.ok (.app 2 none #[.app 1 (some 1) #[.ref 0], .app 0 none #[.ref 0, .ref 1]], 0))
  -- statements
  checkEq "mmb: statement kinds" (file.stmts.toList.map (·.kind))
    [.sort, .sort, .termDef false, .termDef false, .termDef false, .ax, .thm false]
  checkEq "mmb: statement positions" (file.stmts.toList.map fun s => (s.pos, s.bodyStart, s.stop))
    [(0xca, 0xcc, 0xcc), (0xcc, 0xce, 0xce), (0xce, 0xd0, 0xd0), (0xd0, 0xd2, 0xd2),
     (0xd2, 0xd4, 0xd4), (0xd4, 0xd6, 0xdf), (0xdf, 0xe1, 0xef)]
  checkEq "mmb: statement table indices" (file.stmts.toList.map (·.index)) [0, 1, 0, 1, 2, 0, 1]
  -- proof bodies
  checkEq "mmb: proof body of the axiom" (file.proofCmds file.stmts[5]!)
    (.ok #[.ref 1, .ref 0, .ref 1, .term 0 false, .term 2 false])
  checkEq "mmb: proof body of the theorem" (file.proofCmds file.stmts[6]!)
    (.ok #[.ref 0, .ref 0, .term 1 true, .ref 1, .ref 0, .ref 1, .term 0 false, .term 2 false,
      .thm 0 false])
  checkEq "mmb: a statement without a body" (file.proofCmds file.stmts[0]!) (.ok #[])
  -- re-encoding gives the original bytes
  let body := file.stmts[6]!
  checkEq "mmb: re-encoded proof body"
    ((file.proofCmds body).map fun cs => (encodeProof cs).data.toList)
    (.ok (bytes.extract body.bodyStart body.stop).data.toList)
  checkEq "mmb: re-encoded unify stream"
    ((file.thmUnifyCmds 1).map fun cs => (encodeUnify cs).data.toList)
    (.ok (bytes.extract 0xc0 0xca).data.toList)
  -- no index: generated names
  checkEq "mmb: generated names" (file.sortName 1, file.termName 2, file.thmName 0) ("s1", "t2", "T0")
  checkEq "mmb: generated variable names" ((file.termVarNames 0).toList) ["v0", "v1"]

def rejectTests (bytes : ByteArray) : TestM Unit := do
  -- header
  match MmbFile.parse (bytes.extract 0 39) with
  | .ok _ => check "mmb: file shorter than a header" false "accepted"
  | .error e => check "mmb: file shorter than a header" (e.pos == 0 && contains e.msg "header") (toString e)
  rejectsAt "mmb: bad magic" bytes [(0, 0x4c)] 0 "magic"
  rejectsAt "mmb: unknown version" bytes [(4, 2)] 4 "version"
  rejectsAt "mmb: term table inside the sort table" bytes [(0x10, 0x28)] 0x10 "p_terms"
  rejectsAt "mmb: misaligned term table" bytes [(0x10, 0x34)] 0x10 "multiple of 8"
  rejectsAt "mmb: theorem table before the term table" bytes [(0x14, 0x30)] 0x14 "p_thms"
  rejectsAt "mmb: proof stream outside the file" bytes [(0x19, 0x10)] 0x18 "p_proof"
  rejectsAt "mmb: index before the proof stream" bytes [(0x20, 0x10)] 0x20 "p_index"
  rejectsAt "mmb: index outside the file" bytes [(0x21, 0x10)] 0x20 "p_index"
  rejectsAt "mmb: unknown sort modifier bits" bytes [(0x28, 0x14)] 0x28 "modifier"
  rejectsAt "mmb: term data outside the file" bytes [(0x31, 0x20)] 0x30 "term 0"
  rejectsAt "mmb: theorem data outside the file" bytes [(0x4c, 0xf0)] 0x48 "theorem 0"
  -- statements
  rejectsAt "mmb: unknown statement opcode" bytes [(0xca, 0x47)] 0xca "statement opcode"
  rejectsAt "mmb: statement shorter than its command" bytes [(0xcb, 1)] 0xca "length"
  rejectsAt "mmb: sort statement with a body" bytes [(0xcb, 4)] 0xca "sort"
  rejectsAt "mmb: term statement with a body" bytes [(0xcf, 4)] 0xce "not a def"
  rejectsAt "mmb: more sort statements than sorts" bytes [(0xce, 0x44)] 0xce "more sort"
  rejectsAt "mmb: more theorem statements than theorems" bytes [(0xef, 0x46), (0xf0, 0x03), (0xf1, 0x00)]
    0xef "more axiom"
  rejectsAt "mmb: statement running past the end of the file" bytes [(0xe0, 0x40)] 0xdf "end of the file"
  match MmbFile.parse (bytes.extract 0 0xef) with
  | .ok _ => check "mmb: proof stream without a final END" false "accepted"
  | .error e =>
    check "mmb: proof stream without a final END" (e.pos == 0xef && contains e.msg "end of the file")
      (toString e)
  -- proof commands
  rejectsAt "mmb: unknown proof opcode" bytes [(0xdb, 0x1d)] 0xdb "proof command"
  rejectsAt "mmb: unify opcode in a proof" bytes [(0xdb, 0x30)] 0xdb "proof command"
  rejectsAt "mmb: END before the end of the proof" bytes [(0xd8, 0x00)] 0xd8 "END"
  rejectsAt "mmb: proof without END" bytes [(0xde, 0x18)] 0xdf "END"
  rejectsAt "mmb: proof command cut off by the end of the statement" bytes [(0xde, 0x52)] 0xde "END"
  -- unify streams
  rejectsAt "mmb: unknown unify opcode" bytes [(0xa8, 0x74)] 0xa8 "unify command"
  rejectsAt "mmb: proof opcode in a unify stream" bytes [(0xac, 0x10)] 0xac "unify command"
  rejectsAt "mmb: unify reference out of range" bytes [(0xab, 9)] 0xaa "heap"
  rejectsAt "mmb: unify term out of range" bytes [(0xa9, 9)] 0xa8 "term 9"
  rejectsAt "mmb: unify stream ending inside a pattern" bytes [(0xae, 0x00)] 0xae "pattern"
  rejectsAt "mmb: commands after a complete pattern" bytes [(0xb0, 0x32)] 0xb0 "UHyp"
  rejectsAt "mmb: reference to a term that is being read" bytes [(0xc4, 0x72), (0xc5, 0x01)] 0xc4 "cyclic"
  rejectsAt "mmb: UDummy in a theorem" bytes [(0xac, 0x33)] 0xac "UDummy"
  rejectsAt "mmb: UHyp inside a pattern" bytes [(0xaa, 0x36), (0xab, 0x32)] 0xaa "UHyp"

def smallTests : TestM Unit := do
  let bytes ← IO.FS.readBinFile small
  let file ←
    match fullyDecodes bytes with
    | .ok f => pure f
    | .error e => check "mmb: small.mmb decodes" false (toString e); return
  checkEq "mmb: index tables" (file.indexEntries.toList.map (·.type)) ["Name", "VarN", "HypN"]
  checkEq "mmb: sort names" [file.sortName 0, file.sortName 1] ["wff", "set"]
  checkEq "mmb: term names" ((List.range 4).map file.termName) ["imp", "al", "dbl", "allself"]
  checkEq "mmb: theorem names" ((List.range 5).map file.thmName) ["mp", "ax1", "t", "t2", "loc"]
  checkEq "mmb: variable names, dummies after the arguments" (file.termVarNames 3).toList ["ph", "y"]
  checkEq "mmb: hypothesis names" (file.thmHypNames 3).toList ["h1", "h2"]
  checkEq "mmb: a def has a unify stream" (file.termUnifyCmds 3) (.ok #[.term 1 false, .dummy 1, .ref 0])
  checkEq "mmb: value of a def as a pattern" ((file.termValue 3).map (·.concl))
    (.ok (.app 1 none #[.dummy 1 1, .ref 0]))
  -- hypotheses come back in declaration order although the stream stores them reversed
  checkEq "mmb: hypotheses in declaration order" ((file.thmStatement 0).map fun s => (s.concl, s.hyps.toList))
    (.ok (.ref 1, [.ref 0, .app 0 none #[.ref 0, .ref 1]]))
  checkEq "mmb: statement kinds, local theorem last" ((file.stmts.toList.drop 8).map (·.kind))
    [.thm false, .thm false, .thm true]
  checkEq "mmb: proof by conversion" (file.proofCmds file.stmts[8]!)
    (.ok #[.ref 0, .term 2 false, .ref 0, .ref 0, .ref 0, .term 0 true, .thm 1 false, .conv, .ref 1,
      .unfold, .refl])
  -- the dump, against the checked-in text
  let expected ← IO.FS.readFile smallDump
  let out ← IO.mkRef ""
  match ← (dump file fun line => out.modify (· ++ line ++ "\n")).run with
  | .error e => check "mmb: dump of small.mmb" false (toString e)
  | .ok () => checkEq "mmb: dump of small.mmb" (← out.get) expected
  -- a damaged index is an error, a missing name is not
  let pIndex := file.header.pIndex
  rejectsAt "mmb: index header outside the file" bytes [(0x20, 0x76), (0x21, 0x04)] 0x20 "p_index"
  rejectsAt "mmb: index with more entries than fit" bytes [(pIndex, 0x40)] pIndex "index"
  rejectsAt "mmb: Name table outside the file" bytes [(pIndex + 8 + 9, 0x10)] (pIndex + 8) "Name"
  rejectsAt "mmb: duplicate index table" bytes [(pIndex + 8 + 16, 0x4e), (pIndex + 8 + 17, 0x61),
    (pIndex + 8 + 18, 0x6d), (pIndex + 8 + 19, 0x65)] (pIndex + 8 + 16) "twice"
  -- unknown table types are skipped: rename HypN to "Xxxx"
  match fullyDecodes (patch bytes [(pIndex + 8 + 32, 0x58)]) with
  | .error e => check "mmb: unknown index table is skipped" false (toString e)
  | .ok f => checkEq "mmb: unknown index table is skipped" (f.thmHypNames 3).toList ["h0", "h1"]

def readerTests : TestM Unit := do
  let bytes ← IO.FS.readBinFile annotated
  annotatedTests bytes
  rejectTests bytes
  smallTests

end Tests.Mmb
