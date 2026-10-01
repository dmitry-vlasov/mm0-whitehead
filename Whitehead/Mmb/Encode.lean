/-
Encoding of command streams (`docs/MMB-NOTES.md` section 3), the inverse of the stream
decoders in `Whitehead.Mmb.Reader`.

Commands are written in their shortest form, as `mm0-rs` writes them. Decoding a stream
and encoding it again therefore gives back the original bytes for every file written
that way, which is what the acceptance test checks.
-/
import Whitehead.Mmb.Types

namespace Whitehead.Mmb

/-- Appends the command `(op, data)` in its shortest encoding. `op` is at most `0x3F`
and `data` is below `2^32`. -/
def pushCmd (out : ByteArray) (op : UInt8) (data : Nat) : ByteArray :=
  if data == 0 then
    out.push op
  else if data < 0x100 then
    (out.push (op ||| 0x40)).push data.toUInt8
  else if data < 0x10000 then
    ((out.push (op ||| 0x80)).push data.toUInt8).push (data >>> 8).toUInt8
  else
    ((((out.push (op ||| 0xC0)).push data.toUInt8).push (data >>> 8).toUInt8).push
      (data >>> 16).toUInt8).push (data >>> 24).toUInt8

def ProofCmd.push (out : ByteArray) : ProofCmd → ByteArray
  | .term id saved => pushCmd out (if saved then 0x11 else 0x10) id
  | .ref heap => pushCmd out 0x12 heap
  | .dummy sort => pushCmd out 0x13 sort
  | .thm id saved => pushCmd out (if saved then 0x15 else 0x14) id
  | .hyp => out.push 0x16
  | .conv => out.push 0x17
  | .refl => out.push 0x18
  | .symm => out.push 0x19
  | .cong => out.push 0x1A
  | .unfold => out.push 0x1B
  | .convCut => out.push 0x1C
  | .convSave => out.push 0x1E
  | .save => out.push 0x1F
  | .sorry => out.push 0x20

def UnifyCmd.push (out : ByteArray) : UnifyCmd → ByteArray
  | .term id saved => pushCmd out (if saved then 0x31 else 0x30) id
  | .ref heap => pushCmd out 0x32 heap
  | .dummy sort => pushCmd out 0x33 sort
  | .hyp => out.push 0x36

/-- A proof body: the commands, then `END`. -/
def encodeProof (cmds : Array ProofCmd) : ByteArray :=
  (cmds.foldl ProofCmd.push ByteArray.empty).push 0

/-- A unify stream: the commands, then `END`. -/
def encodeUnify (cmds : Array UnifyCmd) : ByteArray :=
  (cmds.foldl UnifyCmd.push ByteArray.empty).push 0

end Whitehead.Mmb
