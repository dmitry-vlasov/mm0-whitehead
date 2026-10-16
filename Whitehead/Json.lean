/-
A small JSON module, for the protocols of the front-ends (JSON-RPC 2.0 over stdio, for
MCP; `docs/DESIGN.md`, "Phase 4", "Front-ends"). Our own, so that the binary does not
depend on the `Lean` package for `Lean.Data.Json` (decided 2026-10-16).

Numbers that are integers are read as `Int`; any other number keeps its text, which is
printed back as it was. Strings are Unicode, with the escapes of RFC 8259, `\u` pairs
for the characters outside the Basic Multilingual Plane included. An object keeps its
members in order.
-/

namespace Whitehead

inductive Json where
  | null
  | bool (b : Bool)
  | int (n : Int)
  /-- A number that is not an integer, as its text. -/
  | float (text : String)
  | str (s : String)
  | arr (xs : Array Json)
  | obj (kvs : Array (String × Json))
  deriving Inhabited, BEq, Repr

namespace Json

/-! ### Reading -/

structure ReadError where
  pos : Nat
  msg : String
  deriving Repr

abbrev ReadM := StateT Nat (Except ReadError)

def fail {α : Type} (msg : String) : ReadM α := do throw ⟨← get, msg⟩

partial def skipWs (cs : Array Char) : ReadM Unit := do
  let i ← get
  if h : i < cs.size then
    let c := cs[i]
    if c == ' ' || c == '\n' || c == '\r' || c == '\t' then
      set (i + 1)
      skipWs cs

def peekChar (cs : Array Char) : ReadM (Option Char) := do return cs[← get]?

def expect (cs : Array Char) (c : Char) : ReadM Unit := do
  if (← peekChar cs) == some c then modify (· + 1) else fail s!"expected `{c}`"

def literal (cs : Array Char) (word : String) : ReadM Unit := do
  for c in word.toList do
    if (← peekChar cs) == some c then modify (· + 1) else fail s!"expected `{word}`"

def hex4 (cs : Array Char) : ReadM Nat := do
  let mut n := 0
  for _ in [0:4] do
    let some c ← peekChar cs | fail "a \\u escape needs four hex digits"
    let d ← if '0' ≤ c && c ≤ '9' then pure (c.toNat - '0'.toNat)
      else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
      else if 'A' ≤ c && c ≤ 'F' then pure (c.toNat - 'A'.toNat + 10)
      else fail "a \\u escape needs four hex digits"
    n := n * 16 + d
    modify (· + 1)
  return n

partial def readString (cs : Array Char) : ReadM String := do
  expect cs '"'
  let mut out := ""
  repeat
    let some c ← peekChar cs | fail "this string is not closed"
    modify (· + 1)
    if c == '"' then break
    if c == '\\' then
      let some e ← peekChar cs | fail "this string is not closed"
      modify (· + 1)
      match e with
      | '"' => out := out.push '"'
      | '\\' => out := out.push '\\'
      | '/' => out := out.push '/'
      | 'b' => out := out.push (Char.ofNat 8)
      | 'f' => out := out.push (Char.ofNat 12)
      | 'n' => out := out.push '\n'
      | 'r' => out := out.push '\r'
      | 't' => out := out.push '\t'
      | 'u' =>
        let hi ← hex4 cs
        if 0xD800 ≤ hi && hi < 0xDC00 then
          -- a surrogate pair: the low half must follow
          literal cs "\\u"
          let lo ← hex4 cs
          if !(0xDC00 ≤ lo && lo < 0xE000) then fail "a high surrogate without its low one"
          out := out.push (Char.ofNat (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)))
        else if 0xDC00 ≤ hi && hi < 0xE000 then fail "a low surrogate without its high one"
        else out := out.push (Char.ofNat hi)
      | _ => fail s!"unknown escape `\\{e}`"
    else if c.toNat < 0x20 then fail "a control character in a string must be escaped"
    else out := out.push c
  return out

def readNumber (cs : Array Char) : ReadM Json := do
  let start ← get
  let isNumChar (c : Char) : Bool := c.isDigit || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E'
  while (← peekChar cs).any isNumChar do modify (· + 1)
  let text := String.ofList (cs.extract start (← get)).toList
  if text.all fun c => c.isDigit || c == '-' then
    match text.toInt? with
    | some n => return .int n
    | none => throw ⟨start, s!"`{text}` is not a number"⟩
  else
    -- the grammar of a number, roughly: a digit somewhere, and nothing else
    if !text.any Char.isDigit then throw ⟨start, s!"`{text}` is not a number"⟩
    return .float text

partial def readValue (cs : Array Char) : ReadM Json := do
  skipWs cs
  let some c ← peekChar cs | fail "expected a value, but the text ends here"
  let v ← match c with
    | '{' =>
      modify (· + 1)
      skipWs cs
      let mut kvs := #[]
      if (← peekChar cs) == some '}' then
        modify (· + 1)
      else
        repeat
          skipWs cs
          let k ← readString cs
          skipWs cs
          expect cs ':'
          let v ← readValue cs
          kvs := kvs.push (k, v)
          skipWs cs
          match ← peekChar cs with
          | some ',' => modify (· + 1)
          | some '}' =>
            modify (· + 1)
            break
          | _ => fail "expected `,` or `}`"
      pure (.obj kvs)
    | '[' =>
      modify (· + 1)
      skipWs cs
      let mut xs := #[]
      if (← peekChar cs) == some ']' then
        modify (· + 1)
      else
        repeat
          xs := xs.push (← readValue cs)
          skipWs cs
          match ← peekChar cs with
          | some ',' => modify (· + 1)
          | some ']' =>
            modify (· + 1)
            break
          | _ => fail "expected `,` or `]`"
      pure (.arr xs)
    | '"' => pure (.str (← readString cs))
    | 't' => do literal cs "true"; pure (.bool true)
    | 'f' => do literal cs "false"; pure (.bool false)
    | 'n' => do literal cs "null"; pure .null
    | _ => if c.isDigit || c == '-' then readNumber cs else fail s!"unexpected `{c}`"
  skipWs cs
  return v

/-- Reads a JSON text: one value, with nothing after it but whitespace. -/
def parse (text : String) : Except ReadError Json := do
  let cs := text.toList.toArray
  let (v, i) ← (readValue cs).run 0
  if i < cs.size then throw ⟨i, "expected the end of the text"⟩
  return v

/-! ### Writing -/

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList[n % 16]!

def escape (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    match c with
    | '"' => out := out ++ "\\\""
    | '\\' => out := out ++ "\\\\"
    | '\n' => out := out ++ "\\n"
    | '\r' => out := out ++ "\\r"
    | '\t' => out := out ++ "\\t"
    | c =>
      if c.toNat < 0x20 then
        out := out ++ "\\u00" ++ String.singleton (hexDigit (c.toNat / 16)) ++ String.singleton (hexDigit c.toNat)
      else out := out.push c
  return out.push '"'

/-- The JSON text of a value, on one line. -/
partial def compress : Json → String
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .int n => toString n
  | .float t => t
  | .str s => escape s
  | .arr xs => "[" ++ ",".intercalate (xs.map compress).toList ++ "]"
  | .obj kvs => "{" ++ ",".intercalate (kvs.map fun (k, v) => escape k ++ ":" ++ compress v).toList ++ "}"

/-! ### Access -/

def get? (j : Json) (key : String) : Option Json :=
  match j with
  | .obj kvs => (kvs.find? (·.1 == key)).map (·.2)
  | _ => none

def str? : Json → Option String
  | .str s => some s
  | _ => none

def nat? : Json → Option Nat
  | .int n => if n ≥ 0 then some n.toNat else none
  | _ => none

def bool? : Json → Option Bool
  | .bool b => some b
  | _ => none

def arr? : Json → Option (Array Json)
  | .arr xs => some xs
  | _ => none

instance : Coe String Json := ⟨.str⟩
instance : Coe Bool Json := ⟨.bool⟩

def ofNat (n : Nat) : Json := .int n

end Json

end Whitehead
