/-
Writing a proof file that differs from a given one only in proof bodies: the header and
the tables are kept, the proof stream is written again. The prover uses this to put the
proofs it has found in the place of the ones that were there.
-/
import Whitehead.Mmb.Reader

namespace Whitehead.Mmb

/-- The statement command with opcode `op` for a body of `bodyLen` bytes: its data is
the distance to the next statement, itself included. -/
def pushStmtCmd (out : ByteArray) (op : UInt8) (bodyLen : Nat) : ByteArray :=
  if 2 + bodyLen < 0x100 then
    (out.push (op ||| 0x40)).push (2 + bodyLen).toUInt8
  else if 3 + bodyLen < 0x10000 then
    let n := 3 + bodyLen
    ((out.push (op ||| 0x80)).push n.toUInt8).push (n >>> 8).toUInt8
  else
    let n := 5 + bodyLen
    ((((out.push (op ||| 0xC0)).push n.toUInt8).push (n >>> 8).toUInt8).push (n >>> 16).toUInt8).push
      (n >>> 24).toUInt8

/-- The file `f` with the body of statement `i` replaced by `bodies[i]` where that is
given (a body ends with its `END`). The index is dropped: the offsets in it would be
wrong. -/
def MmbFile.withBodies (f : MmbFile) (bodies : Array (Option ByteArray)) : ByteArray := Id.run do
  let b := f.bytes
  let h := f.header
  let mut out := b.extract 0 h.pProof
  -- no index: the pointer is the 8 bytes at offset 32
  for k in [0:8] do
    out := out.set! (32 + k) 0
  for i in [0:f.stmts.size] do
    let s := f.stmts[i]!
    match bodies[i]?.join with
    | some body =>
      out := pushStmtCmd out (b.get! s.pos &&& 0x3F) body.size
      out := out ++ body
    | none => out := out ++ b.extract s.pos s.stop
  -- the END of the proof stream, and the padding that follows it
  out := out.push 0
  while out.size % 8 != 0 do
    out := out.push 0
  return out ++ ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0]

end Whitehead.Mmb
