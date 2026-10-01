/-
Mutations of a proof file, for differential testing.

A mutant is a valid `.mmb` file with one small change: a flipped bit, two proof commands
swapped, an opcode or an operand altered, a broken binder. The changes are aimed at the
parts of the file by structure rather than spread evenly over its bytes, so that the
small tables get as much attention as the long proof stream. The index is left alone:
nothing in it affects whether a proof is valid, and `mm0-rs` takes names from it.

Everything is determined by a seed.
-/
import Whitehead.Mmb.Reader

open Whitehead.Mmb

namespace Tests.Mutate

/-- A small deterministic generator (a 64-bit linear congruential one). -/
structure Rng where
  state : UInt64
  deriving Inhabited

namespace Rng

def next (r : Rng) : Rng :=
  ⟨r.state * 6364136223846793005 + 1442695040888963407⟩

/-- A number below `n` (which must be positive), and the next generator. -/
def below (r : Rng) (n : Nat) : Nat × Rng :=
  let r := r.next
  ((r.state >>> 33).toNat % n, r)

end Rng

/-- A mutant and what was done to make it. -/
structure Mutant where
  bytes : ByteArray
  what : String
  deriving Inhabited

/-- The start offsets of the commands of a stream from `pos` up to its `END` (not
included), reading at most up to `stop`. -/
partial def cmdOffsets (b : ByteArray) (pos stop : Nat) (acc : Array Nat) : Array Nat :=
  if pos ≥ stop then acc
  else
    match Reader.readCmd b pos with
    | .error _ => acc
    | .ok (op, _, next) => if op == 0 then acc else cmdOffsets b next stop (acc.push pos)

def flipBit (b : ByteArray) (pos bit : Nat) : ByteArray :=
  b.set! pos (b.get! pos ^^^ ((1 : UInt8) <<< bit.toUInt8))

/-- Flips one bit of a byte in `[lo, hi)`. -/
def flipIn (f : MmbFile) (lo hi : Nat) (region : String) (r : Rng) : Option Mutant × Rng :=
  if hi ≤ lo then (none, r)
  else
    let (off, r) := r.below (hi - lo)
    let (bit, r) := r.below 8
    (some ⟨flipBit f.bytes (lo + off) bit, s!"flip bit {bit} at 0x{hex (lo + off)} ({region})"⟩, r)

/-- A statement that has a proof body. -/
def pickBody (f : MmbFile) (r : Rng) : Option Stmt × Rng :=
  let withBody := f.stmts.filter f.hasBody
  if withBody.isEmpty then (none, r)
  else
    let (i, r) := r.below withBody.size
    (some withBody[i]!, r)

/-- Where the unify stream of a random def or theorem starts. -/
def pickUnify (f : MmbFile) (r : Rng) : Option Nat × Rng :=
  let defs := (Array.range f.terms.size).filter (f.terms[·]!.isDef)
  let total := defs.size + f.thms.size
  if total == 0 then (none, r)
  else
    let (i, r) := r.below total
    (some (if i < defs.size then f.termUnifyPos defs[i]! else f.thmUnifyPos (i - defs.size)), r)

/-- The offset of a random binder or return-type word. -/
def pickArgWord (f : MmbFile) (r : Rng) : Option Nat × Rng :=
  let total := f.terms.size + f.thms.size
  if total == 0 then (none, r)
  else
    let (i, r) := r.below total
    let (pData, count) :=
      if i < f.terms.size then (f.terms[i]!.pData, f.terms[i]!.numArgs + 1)
      else (f.thms[i - f.terms.size]!.pData, f.thms[i - f.terms.size]!.numArgs)
    if count == 0 then (none, r)
    else
      let (k, r) := r.below count
      (some (pData + 8 * k), r)

/-- The proof opcodes, to replace one by another. -/
def proofOpcodes : Array UInt8 :=
  #[0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1E, 0x1F, 0x20]

/-- Adds or subtracts one from the operand of the command at `pos`, in its own width. -/
def bumpData (b : ByteArray) (pos : Nat) (up : Bool) : Option ByteArray :=
  let width := (b.get! pos >>> 6).toNat
  if width == 0 then none
  else
    let delta : UInt8 := if up then 1 else 255
    some (b.set! (pos + 1) (b.get! (pos + 1) + delta))

/-- One mutation of the file. `none` if the kind drawn does not apply to this file. -/
def mutateOnce (f : MmbFile) (r : Rng) : Option Mutant × Rng :=
  let b := f.bytes
  let h := f.header
  -- the proof stream ends with the END after the last statement; what follows, up to the
  -- index, is the data of the index (names), which is not touched
  let limit := match f.stmts.back? with
    | some s => s.stop + 1
    | none => h.pProof + 1
  let (kind, r) := r.below 14
  match kind with
  | 0 => flipIn f 0 40 "header" r
  | 1 => flipIn f 40 (40 + h.numSorts) "sort table" r
  | 2 => flipIn f h.pTerms (h.pTerms + 8 * h.numTerms) "term table" r
  | 3 => flipIn f h.pThms (h.pThms + 8 * h.numThms) "theorem table" r
  | 4 => flipIn f (h.pThms + 8 * h.numThms) h.pProof "binders and unify streams" r
  | 5 | 6 => flipIn f h.pProof limit "proof stream" r
  | 7 =>
    -- swap two adjacent proof commands
    match pickBody f r with
    | (none, r) => (none, r)
    | (some s, r) =>
      let offs := cmdOffsets b s.bodyStart s.stop #[]
      if offs.size < 2 then (none, r)
      else
        let (i, r) := r.below (offs.size - 1)
        let a := offs[i]!
        let m := offs[i + 1]!
        let e := if i + 2 < offs.size then offs[i + 2]! else s.stop - 1
        let swapped := (b.extract 0 a) ++ (b.extract m e) ++ (b.extract a m) ++ (b.extract e b.size)
        if swapped == b then (none, r)
        else (some ⟨swapped, s!"swap the proof commands at 0x{hex a} and 0x{hex m}"⟩, r)
  | 8 | 9 =>
    -- replace the opcode of a proof command, or turn a saving command into a plain one
    match pickBody f r with
    | (none, r) => (none, r)
    | (some s, r) =>
      let offs := cmdOffsets b s.bodyStart s.stop #[]
      if offs.isEmpty then (none, r)
      else
        let (i, r) := r.below offs.size
        let pos := offs[i]!
        let first := b.get! pos
        let op := first &&& 0x3F
        if kind == 9 && (op == 0x11 || op == 0x15) then
          (some ⟨b.set! pos (first - 1), s!"drop the save of the command at 0x{hex pos}"⟩, r)
        else
          let (k, r) := r.below proofOpcodes.size
          let op' := proofOpcodes[k]!
          if op' == op then (none, r)
          else (some ⟨b.set! pos ((first &&& 0xC0) ||| op'),
                      s!"opcode 0x{hex op.toNat} -> 0x{hex op'.toNat} at 0x{hex pos}"⟩, r)
  | 10 =>
    -- change the operand of a proof command by one
    match pickBody f r with
    | (none, r) => (none, r)
    | (some s, r) =>
      let offs := cmdOffsets b s.bodyStart s.stop #[]
      if offs.isEmpty then (none, r)
      else
        let (i, r) := r.below offs.size
        let (up, r) := r.below 2
        match bumpData b offs[i]! (up == 1) with
        | some b' => (some ⟨b', s!"operand {if up == 1 then "+" else "-"}1 of the proof command at 0x{hex offs[i]!}"⟩, r)
        | none => (none, r)
  | 11 =>
    -- change the operand of a unify command by one: an altered statement
    match pickUnify f r with
    | (none, r) => (none, r)
    | (some start, r) =>
      let offs := cmdOffsets b start b.size #[]
      if offs.isEmpty then (none, r)
      else
        let (i, r) := r.below offs.size
        let (up, r) := r.below 2
        match bumpData b offs[i]! (up == 1) with
        | some b' => (some ⟨b', s!"operand {if up == 1 then "+" else "-"}1 of the unify command at 0x{hex offs[i]!}"⟩, r)
        | none => (none, r)
  | 12 =>
    -- break a binder: a dependency bit, the bound flag, or the sort
    match pickArgWord f r with
    | (none, r) => (none, r)
    | (some pos, r) =>
      let (which, r) := r.below 4
      if which == 0 then (some ⟨flipBit b (pos + 7) 7, s!"flip the bound flag of the binder at 0x{hex pos}"⟩, r)
      else if which == 1 then (some ⟨flipBit b (pos + 7) 0, s!"change the sort of the binder at 0x{hex pos}"⟩, r)
      else
        let (bit, r) := r.below 4
        (some ⟨flipBit b pos bit, s!"flip dependency bit {bit} of the binder at 0x{hex pos}"⟩, r)
  | _ =>
    -- cut the file off inside the proof stream
    if limit ≤ h.pProof + 1 || h.pIndex != 0 then (none, r)
    else
      let (off, r) := r.below (limit - h.pProof - 1)
      (some ⟨b.extract 0 (h.pProof + 1 + off), s!"truncate at 0x{hex (h.pProof + 1 + off)}"⟩, r)

/-- The next mutant of the file: draws until a mutation applies. -/
partial def nextMutant (f : MmbFile) (r : Rng) : Mutant × Rng :=
  match mutateOnce f r with
  | (some m, r) => (m, r)
  | (none, r) => nextMutant f r

end Tests.Mutate
