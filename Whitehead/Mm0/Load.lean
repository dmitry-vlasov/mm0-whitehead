/-
Loading a `.mm0` specification together with the files it imports.

`import "file";` is an extension of `mm0-rs` and is not in `mm0.md`. Its meaning here is
the one of `mm0-rs join`: textual inclusion at the place of the statement, with the path
taken relative to the directory of the importing file, and with a file that has already
been included skipped on any later import. The result is the statement list that a
verifier of plain MM0 would see.

One difference from `mm0-rs join`: every import cycle is an error here. `join` reports a
cycle only if it goes through the file it started from, and silently skips the others;
`mm0-rs compile` reports them all.
-/
import Whitehead.Mm0.Parser

namespace Whitehead.Mm0

/-- One file of a specification. -/
structure Source where
  /-- The path as it was reached: the root as given, an import relative to its importer. -/
  path : System.FilePath
  bytes : ByteArray
  deriving Inhabited

/-- A statement and the index, in `Spec.sources`, of the file it stands in. Spans in the
statement are offsets into that file. -/
structure Located where
  file : Nat
  stmt : Stmt

/-- A specification with its imports resolved: no `import` statement is left. -/
structure Spec where
  sources : Array Source
  stmts : Array Located

inductive LoadError where
  /-- The root file cannot be read. -/
  | io (path : System.FilePath) (msg : String)
  /-- A file does not parse. -/
  | parse (source : Source) (err : ParseError)
  /-- The file named by an `import` cannot be read. `at_` is the string literal. -/
  | importIo (source : Source) (at_ : Span) (path : String) (msg : String)
  /-- An `import` leads back to a file that is still being read. `chain` runs from that
  file to the file containing the offending `import`. -/
  | cycle (source : Source) (at_ : Span) (chain : Array System.FilePath)

def LoadError.format : LoadError → String
  | .io path msg => s!"{path}: error: cannot read the file: {msg}"
  | .parse source err => err.format source.path.toString source.bytes
  | .importIo source at_ path msg =>
    (ParseError.mk at_.start s!"cannot read the imported file \"{path}\": {msg}").format
      source.path.toString source.bytes
  | .cycle source at_ chain =>
    let names := " -> ".intercalate ((chain.push chain[0]!).toList.map (·.toString))
    (ParseError.mk at_.start s!"import cycle: {names}").format source.path.toString source.bytes

namespace Load

structure State where
  sources : Array Source := #[]
  stmts : Array Located := #[]
  /-- The canonical paths of the files included so far, finished or not. -/
  seen : Array System.FilePath := #[]

/-- Reads the file `path`, whose canonical path is `real`, and appends its statements,
with the imports expanded, to the state. `stack` holds the canonical paths of the files
that are being read, the root first; `shown` holds their paths as reached. -/
partial def loadFile (path real : System.FilePath) (bytes : ByteArray)
    (stack shown : Array System.FilePath) (st : State) : IO (Except LoadError State) := do
  let source : Source := ⟨path, bytes⟩
  let file := st.sources.size
  let mut st := { st with sources := st.sources.push source, seen := st.seen.push real }
  let stack := stack.push real
  let shown := shown.push path
  let mut ps ←
    match Parser.init bytes with
    | .ok ps => pure ps
    | .error e => return .error (.parse source e)
  repeat
    match Parser.parseStmt?.run ps with
    | .error e _ => return .error (.parse source e)
    | .ok none _ => break
    | .ok (some stmt) ps' =>
      ps := ps'
      match stmt.kind with
      | .importFile rel at_ =>
        let target := match path.parent with
          | some dir => dir / rel
          | none => (rel : System.FilePath)
        let (targetReal, targetBytes) ←
          try
            let r ← IO.FS.realPath target
            pure (r, ← IO.FS.readBinFile r)
          catch e => return .error (.importIo source at_ rel (toString e))
        match stack.findIdx? (· == targetReal) with
        | some i => return .error (.cycle source at_ (shown.extract i shown.size))
        | none =>
          if !st.seen.contains targetReal then
            match ← loadFile target targetReal targetBytes stack shown st with
            | .ok st' => st := st'
            | .error e => return .error e
      | _ => st := { st with stmts := st.stmts.push ⟨file, stmt⟩ }
  return .ok st

end Load

/-- Loads the specification in `path` and everything it imports. -/
def load (path : System.FilePath) : IO (Except LoadError Spec) := do
  let (real, bytes) ←
    try
      let r ← IO.FS.realPath path
      pure (r, ← IO.FS.readBinFile r)
    catch e => return .error (.io path (toString e))
  match ← Load.loadFile path real bytes #[] #[] {} with
  | .ok st => return .ok ⟨st.sources, st.stmts⟩
  | .error e => return .error e

end Whitehead.Mm0
