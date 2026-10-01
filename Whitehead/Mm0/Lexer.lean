/-
The primary lexer of `.mm0` files ("Lexical structure" in `mm0.md`).

It works on the bytes of the file. The grammar is ASCII outside math strings, so byte
offsets serve as source positions and no decoding is needed until a lexeme is cut out.
The lexer is a function from a position to the next token: the parser pulls tokens one
at a time, and no token array is built for a whole file.
-/
import Whitehead.Mm0.Syntax

namespace Whitehead.Mm0

inductive TokenKind where
  /-- `[a-zA-Z_][a-zA-Z0-9_]*`, except the single character `_`. Pseudo-keywords such
  as `sort` are identifiers too; the parser tells them apart by position. -/
  | ident (name : String)
  /-- `0 | [1-9][0-9]*` -/
  | number (n : Nat)
  /-- `'$' [^$]* '$'`; `text` is what stands between the two `$`. -/
  | math (text : String)
  /-- One of `* . : ; ( ) > { } = _`. -/
  | sym (c : Char)
  /-- A string literal `"..."`, with its escapes resolved. Not part of `mm0.md`: it
  exists for the `import` statement, an extension of `mm0-rs`. -/
  | str (value : String)
  | eof
  deriving Repr, BEq, Inhabited

structure Token where
  kind : TokenKind
  span : Span
  deriving Repr, Inhabited

namespace Lexer

@[inline] def isIdentStart (c : UInt8) : Bool :=
  (0x41 ≤ c && c ≤ 0x5A) || (0x61 ≤ c && c ≤ 0x7A) || c == 0x5F

@[inline] def isDigit (c : UInt8) : Bool :=
  0x30 ≤ c && c ≤ 0x39

@[inline] def isIdentRest (c : UInt8) : Bool :=
  isIdentStart c || isDigit c

@[inline] def isSymbol (c : UInt8) : Bool :=
  c == 0x2A || c == 0x2E || c == 0x3A || c == 0x3B || c == 0x28 || c == 0x29 ||
  c == 0x3E || c == 0x7B || c == 0x7D || c == 0x3D

/-- The first position at or after `pos` whose byte does not satisfy `p`. -/
partial def scanWhile (src : ByteArray) (p : UInt8 → Bool) (pos : Nat) : Nat :=
  if pos < src.size && p (src.get! pos) then scanWhile src p (pos + 1) else pos

/-- Skips whitespace (space and newline only) and `--` line comments. A comment runs up
to and including a newline; one that is cut off by the end of the file is an error, as
in `mm0.md` and in the formal specification (`regexLineComment`). -/
partial def skipWs (src : ByteArray) (pos : Nat) : Except ParseError Nat :=
  if pos < src.size then
    let c := src.get! pos
    if c == 0x20 || c == 0x0A then
      skipWs src (pos + 1)
    else if c == 0x2D && pos + 1 < src.size && src.get! (pos + 1) == 0x2D then
      let stop := scanWhile src (· != 0x0A) (pos + 2)
      if stop < src.size then skipWs src (stop + 1)
      else .error ⟨pos, "a comment must end with a newline"⟩
    else .ok pos
  else .ok pos

def describeByte (c : UInt8) : String :=
  if c == 0x00 then "NUL"
  else if c == 0x09 then "tab"
  else if c == 0x0D then "carriage return"
  else if c ≥ 0x80 then s!"non-ASCII byte 0x{String.ofList (Nat.toDigits 16 c.toNat)}"
  else if c < 0x20 || c == 0x7F then s!"control character 0x{String.ofList (Nat.toDigits 16 c.toNat)}"
  else s!"`{Char.ofNat c.toNat}`"

/-- The value of the decimal digits in `[pos, stop)`. -/
partial def decimal (src : ByteArray) (pos stop : Nat) (acc : Nat := 0) : Nat :=
  if pos < stop then decimal src (pos + 1) stop (acc * 10 + (src.get! pos).toNat - 0x30) else acc

def hexDigit (c : UInt8) : Option UInt8 :=
  if isDigit c then some (c - 0x30)
  else if 0x41 ≤ c && c ≤ 0x46 then some (c - 0x41 + 10)
  else if 0x61 ≤ c && c ≤ 0x66 then some (c - 0x61 + 10)
  else none

/-- The contents of a string literal whose opening `"` is at `start`, and the position
after its closing `"`. The escapes are those of `mm0-rs`: `\\`, `\"`, `\n`, `\r` and
`\xHH`. `mm0-rs` warns about any other escape and keeps the backslash; here it is an
error. `pos` is the next byte to read and `acc` the bytes collected so far. -/
partial def scanString (src : ByteArray) (start pos : Nat) (acc : ByteArray) :
    Except ParseError (ByteArray × Nat) :=
  if pos ≥ src.size then
    .error ⟨start, "unclosed string literal"⟩
  else
    let c := src.get! pos
    if c == 0x22 then
      .ok (acc, pos + 1)
    else if c == 0x5C then
      if pos + 1 ≥ src.size then
        .error ⟨start, "unclosed string literal"⟩
      else
        let e := src.get! (pos + 1)
        if e == 0x5C || e == 0x22 then scanString src start (pos + 2) (acc.push e)
        else if e == 0x6E then scanString src start (pos + 2) (acc.push 0x0A)
        else if e == 0x72 then scanString src start (pos + 2) (acc.push 0x0D)
        else if (e == 0x78 || e == 0x58) && pos + 3 < src.size then
          match hexDigit (src.get! (pos + 2)), hexDigit (src.get! (pos + 3)) with
          | some h, some l => scanString src start (pos + 4) (acc.push (h * 16 + l))
          | _, _ => .error ⟨pos, "invalid hex escape in a string literal: expected `\\xHH`"⟩
        else
          .error ⟨pos, "unknown escape sequence in a string literal"⟩
    else
      scanString src start (pos + 1) (acc.push c)

/-- The token that starts at or after `pos`, after skipping whitespace and comments. -/
def nextToken (src : ByteArray) (pos : Nat) : Except ParseError Token := do
  let start ← skipWs src pos
  if start ≥ src.size then
    .ok ⟨.eof, ⟨start, start⟩⟩
  else
    let c := src.get! start
    if isIdentStart c then
      let stop := scanWhile src isIdentRest (start + 1)
      if c == 0x5F && stop == start + 1 then
        .ok ⟨.sym '_', ⟨start, stop⟩⟩
      else
        .ok ⟨.ident (String.fromUTF8! (src.extract start stop)), ⟨start, stop⟩⟩
    else if isDigit c then
      let stop := scanWhile src isDigit (start + 1)
      if c == 0x30 && stop > start + 1 then
        .error ⟨start, "a number may not have a leading zero"⟩
      else if stop < src.size && isIdentRest (src.get! stop) then
        .error ⟨stop, "invalid number: a letter or `_` directly after the digits"⟩
      else
        .ok ⟨.number (decimal src start stop), ⟨start, stop⟩⟩
    else if c == 0x24 then
      let stop := scanWhile src (· != 0x24) (start + 1)
      if stop ≥ src.size then
        .error ⟨start, "unterminated math string: no closing `$`"⟩
      else
        match String.fromUTF8? (src.extract (start + 1) stop) with
        | some text => .ok ⟨.math text, ⟨start, stop + 1⟩⟩
        | none => .error ⟨start, "this math string is not valid UTF-8"⟩
    else if c == 0x22 then
      let (bytes, stop) ← scanString src start (start + 1) ByteArray.empty
      match String.fromUTF8? bytes with
      | some value => .ok ⟨.str value, ⟨start, stop⟩⟩
      | none => .error ⟨start, "this string literal is not valid UTF-8"⟩
    else if isSymbol c then
      .ok ⟨.sym (Char.ofNat c.toNat), ⟨start, start + 1⟩⟩
    else
      .error ⟨start, s!"illegal character {describeByte c}"⟩

/-- All tokens of `src`, the last one being `eof`. For tests and debugging; the parser
does not use it. -/
partial def tokenize (src : ByteArray) : Except ParseError (Array Token) :=
  let rec go (pos : Nat) (acc : Array Token) : Except ParseError (Array Token) :=
    match nextToken src pos with
    | .error e => .error e
    | .ok t =>
      let acc := acc.push t
      match t.kind with
      | .eof => .ok acc
      | _ => go t.span.stop acc
  go 0 #[]

end Lexer

/-- The 1-based line and column (in bytes) of byte offset `pos`. -/
def lineCol (src : ByteArray) (pos : Nat) : Nat × Nat := Id.run do
  let mut line := 1
  let mut lineStart := 0
  for i in [0:min pos src.size] do
    if src.get! i == 0x0A then
      line := line + 1
      lineStart := i + 1
  return (line, pos - lineStart + 1)

/-- `file:line:col: error: msg`, followed by the source line and a caret under the
position. -/
def ParseError.format (e : ParseError) (file : String) (src : ByteArray) : String :=
  let (line, col) := lineCol src e.pos
  let lineStart := e.pos - (col - 1)
  let lineEnd := Lexer.scanWhile src (· != 0x0A) lineStart
  let text := (String.fromUTF8? (src.extract lineStart lineEnd)).getD "<line is not valid UTF-8>"
  s!"{file}:{line}:{col}: error: {e.msg}\n  {text}\n  {String.ofList (List.replicate (col - 1) ' ')}^"

end Whitehead.Mm0
