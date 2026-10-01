/-
The data of a `.mmb` proof file, as decoded by `Whitehead.Mmb.Reader`.

`docs/MMB-NOTES.md` describes the format; section numbers below refer to it.
-/
namespace Whitehead.Mmb

/-- An error of the reader, at a byte offset of the file. -/
structure MmbError where
  pos : Nat
  msg : String
  deriving Repr, BEq, Inhabited

def hex (n : Nat) : String :=
  String.ofList (Nat.toDigits 16 n)

/-- `file:0x<offset>: error: msg` -/
def MmbError.format (e : MmbError) (file : String) : String :=
  s!"{file}:0x{hex e.pos}: error: {e.msg}"

/-- The modifiers of a sort: one byte of the sort table (section 2). -/
structure SortData where
  raw : UInt8
  deriving BEq, Inhabited

namespace SortData
def isPure (s : SortData) : Bool := s.raw &&& 1 != 0
def isStrict (s : SortData) : Bool := s.raw &&& 2 != 0
def isProvable (s : SortData) : Bool := s.raw &&& 4 != 0
def isFree (s : SortData) : Bool := s.raw &&& 8 != 0
end SortData

/-- An `arg` word: a binder or a return type (section 2). -/
structure Arg where
  raw : UInt64
  deriving BEq, Inhabited

namespace Arg
/-- Bit 63: a bound variable. -/
def bound (a : Arg) : Bool := a.raw >>> 63 != 0
/-- Bits 56–62: the sort. -/
def sort (a : Arg) : Nat := ((a.raw >>> 56) &&& 0x7F).toNat
/-- Bits 0–54: the set of bound variables depended on, bit `j` for the `j`-th one. -/
def deps (a : Arg) : UInt64 := a.raw &&& 0x7FFFFFFFFFFFFF
/-- Bit 55, which must be zero. -/
def reservedBit (a : Arg) : Bool := (a.raw >>> 55) &&& 1 != 0
end Arg

structure Header where
  numSorts : Nat
  numTerms : Nat
  numThms : Nat
  pTerms : Nat
  pThms : Nat
  pProof : Nat
  pIndex : Nat
  /-- The two reserved fields, which should be zero. -/
  reserved : Nat
  reserved2 : Nat
  deriving Repr, Inhabited

/-- An entry of the term table. The binders, the return type and, for a def, the unify
stream are at `pData` and are read on demand. -/
structure TermEntry where
  numArgs : Nat
  /-- The result sort as the table has it (the low seven bits of the sort byte). -/
  sort : Nat
  isDef : Bool
  reserved : Nat
  pData : Nat
  deriving Repr, Inhabited

/-- An entry of the theorem table. The binders and the unify stream are at `pData`. -/
structure ThmEntry where
  numArgs : Nat
  reserved : Nat
  pData : Nat
  deriving Repr, Inhabited

/-- A command of a unify stream (section 4). -/
inductive UnifyCmd where
  | term (id : Nat) (save : Bool)
  | ref (heap : Nat)
  | dummy (sort : Nat)
  | hyp
  deriving Repr, BEq, Inhabited

/-- A command of a proof body (section 5). -/
inductive ProofCmd where
  | term (id : Nat) (save : Bool)
  | ref (heap : Nat)
  | dummy (sort : Nat)
  | thm (id : Nat) (save : Bool)
  | hyp
  | conv
  | refl
  | symm
  | cong
  | unfold
  | convCut
  | convSave
  | save
  | sorry
  deriving Repr, BEq, Inhabited

inductive StmtKind where
  | sort
  /-- `Term`/`Def` (`0x05`) or `LocalDef` (`0x0D`); the table entry says whether it is a def. -/
  | termDef (isLocal : Bool)
  | ax
  /-- `Thm` (`0x06`) or `LocalThm` (`0x0E`). -/
  | thm (isLocal : Bool)
  deriving Repr, BEq, Inhabited

/-- A statement of the proof stream. -/
structure Stmt where
  kind : StmtKind
  /-- The offset of the statement command. -/
  pos : Nat
  /-- The first byte after the statement command: the proof body, if there is one. -/
  bodyStart : Nat
  /-- The offset of the next statement. The body, with its `END`, is `[bodyStart, stop)`. -/
  stop : Nat
  /-- Which sort, term or theorem this statement declares: an index into that table. -/
  index : Nat
  deriving Repr, Inhabited

/-- A unify stream read as a tree (section 4). Heap indices are those of the stream: the
arguments first, then one for every saved term and dummy, in stream order. -/
inductive Pattern where
  | ref (heap : Nat)
  | dummy (sort : Nat) (heap : Nat)
  /-- `save` is the heap index the term gets, if the command was `UTermSave`. -/
  | app (term : Nat) (save : Option Nat) (args : Array Pattern)
  deriving Repr, BEq, Inhabited

/-- The contents of a unify stream: the value of a def (no hypotheses), or the conclusion
and the hypotheses of an axiom or theorem, the hypotheses in declaration order. -/
structure Statement where
  concl : Pattern
  hyps : Array Pattern
  /-- The sorts of the dummies, in the order of their `UDummy` commands. -/
  dummies : Array Nat
  deriving Repr, Inhabited

/-- An entry of the index (section 7). -/
structure IndexEntry where
  /-- The four bytes of the table type, as text. -/
  type : String
  data : Nat
  ptr : Nat
  deriving Repr, Inhabited

/-- The names found in the index. An array is empty if its table is absent; a name is
`none` if its pointer is null or does not lead to a string. -/
structure Names where
  sorts : Array (Option String) := #[]
  terms : Array (Option String) := #[]
  thms : Array (Option String) := #[]
  /-- Per term: its arguments, then its dummies. -/
  termVars : Array (Array (Option String)) := #[]
  /-- Per theorem: its arguments, then its dummies. -/
  thmVars : Array (Array (Option String)) := #[]
  /-- Per theorem: its hypotheses. -/
  thmHyps : Array (Array (Option String)) := #[]
  deriving Inhabited

/-- An opened `.mmb` file. The tables are decoded; binders, unify streams and proof bodies
stay in `bytes` and are read by the functions of `Whitehead.Mmb.Reader`. -/
structure MmbFile where
  bytes : ByteArray
  header : Header
  sorts : Array SortData
  terms : Array TermEntry
  thms : Array ThmEntry
  stmts : Array Stmt
  indexEntries : Array IndexEntry
  names : Names
  deriving Inhabited

end Whitehead.Mmb
