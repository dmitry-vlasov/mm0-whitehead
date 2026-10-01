import Whitehead

open Whitehead

def usage : String :=
  "usage: mm0-whitehead <command> [arguments]

  dump <file.mm0>                print the parsed statements of a specification file
  join <file.mm0>                print a specification with its imports included
  dump <file.mmb>                print a decoded proof file: statements and proofs
  verify <file.mmb>              check the proofs of a proof file, without a specification
  verify <file.mm0> <file.mmb>   check that a proof file proves a specification
  prove ...                      automated proof search                        (phase 3)
  bench <file> ...               time the .mm0 front end or the .mmb reader on the given files"

/-- Exit codes: 0 success, 1 the input was rejected, 2 the command line is wrong or asks
for something that does not exist yet. -/
def notImplemented (what : String) : IO UInt32 := do
  IO.eprintln s!"mm0-whitehead: not implemented yet: {what}"
  return 2

def dumpMm0 (path : String) : IO UInt32 := do
  let src ← IO.FS.readBinFile path
  match Mm0.parse src with
  | .ok stmts =>
    IO.print (Mm0.printStmts stmts)
    return 0
  | .error e =>
    IO.eprintln (e.format path src)
    return 1

def joinMm0 (path : String) : IO UInt32 := do
  match ← Mm0.load path with
  | .ok spec =>
    IO.print (Mm0.printStmts (spec.stmts.map (·.stmt)))
    return 0
  | .error e =>
    IO.eprintln e.format
    return 1

def dumpMmb (path : String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile path
  let out ← IO.getStdout
  let result ←
    match Mmb.MmbFile.parse bytes with
    | .error e => pure (.error e)
    | .ok file => (Mmb.dump file fun line => out.putStrLn line).run
  match result with
  | .ok () => return 0
  | .error e =>
    out.flush
    IO.eprintln (e.format path)
    return 1

def dump (path : String) : IO UInt32 :=
  match (path : System.FilePath).extension with
  | some "mm0" => dumpMm0 path
  | some "mmb" => dumpMmb path
  | _ => do
    IO.eprintln s!"mm0-whitehead: dump: expected a .mm0 or .mmb file, got {path}"
    return 2

def benchMm0 (path : String) : IO UInt32 := do
  let src ← IO.FS.readBinFile path
  let start ← IO.monoNanosNow
  let result := Mm0.parse src
  let count ←
    match result with
    | .ok stmts => pure stmts.size
    | .error e =>
      IO.eprintln (e.format path src)
      return 1
  let nanos := (← IO.monoNanosNow) - start
  let micros := nanos / 1000
  let mbPerSec := if nanos == 0 then 0 else src.size * 1000 / nanos
  IO.println s!"{path}: {src.size} bytes, {count} statements, \
    parse {micros / 1000}.{(micros % 1000) / 100} ms, {mbPerSec} MB/s"
  -- the whole front end: imports resolved, every formula parsed
  let start ← IO.monoNanosNow
  let spec ←
    match ← Mm0.load path with
    | .ok spec => pure spec
    | .error e =>
      IO.eprintln e.format
      return 1
  match Mm0.elaborate spec with
  | .error e =>
    IO.eprintln e.format
    return 1
  | .ok env =>
    let micros := ((← IO.monoNanosNow) - start) / 1000
    IO.println s!"{path}: load and elaborate {micros / 1000}.{(micros % 1000) / 100} ms: \
      {env.sorts.size} sorts, {env.terms.size} terms, {env.thms.size} axioms and theorems"
  return 0

/-- Times opening a `.mmb` file and decoding every stream in it. -/
def benchMmb (path : String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile path
  let start ← IO.monoNanosNow
  let file ←
    match Mmb.MmbFile.parse bytes with
    | .ok file => pure file
    | .error e =>
      IO.eprintln (e.format path)
      return 1
  let opened ← IO.monoNanosNow
  if let .error e := file.checkStreams then
    IO.eprintln (e.format path)
    return 1
  let done ← IO.monoNanosNow
  let ms (nanos : Nat) : String := s!"{nanos / 1000000}.{(nanos % 1000000) / 100000} ms"
  let nanos := done - start
  let mbPerSec := if nanos == 0 then 0 else bytes.size * 1000 / nanos
  IO.println s!"{path}: {bytes.size} bytes, {file.stmts.size} statements, \
    open {ms (opened - start)}, decode all streams {ms (done - opened)}, {mbPerSec} MB/s"
  return 0

/-- Checks the proofs of a `.mmb` file on their own. -/
def verifyMmb (path : String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile path
  let start ← IO.monoNanosNow
  match Mmb.MmbFile.parse bytes with
  | .error e =>
    IO.eprintln (e.format path)
    return 1
  | .ok file =>
    match Verify.checkProofs file with
    | .error e =>
      IO.eprintln (e.format file path)
      return 1
    | .ok () =>
      let micros := ((← IO.monoNanosNow) - start) / 1000
      IO.println s!"{path}: {file.stmts.size} statements verified in {micros / 1000}.{(micros % 1000) / 100} ms \
        (proofs only: no specification was given)"
      return 0

/-- The verifier: the proofs of `mmb` are valid, and they prove what `mm0` states. -/
def verifyPair (mm0 mmb : String) : IO UInt32 := do
  let start ← IO.monoNanosNow
  let env ←
    match ← Mm0.load mm0 with
    | .error e =>
      IO.eprintln e.format
      return 1
    | .ok spec =>
      match Mm0.elaborate spec with
      | .error e =>
        IO.eprintln e.format
        return 1
      | .ok env => pure env
  let elaborated ← IO.monoNanosNow
  let bytes ← IO.FS.readBinFile mmb
  let file ←
    match Mmb.MmbFile.parse bytes with
    | .error e =>
      IO.eprintln (e.format mmb)
      return 1
    | .ok file => pure file
  if let .error e := Verify.checkProofs file then
    IO.eprintln (e.format file mmb)
    return 1
  let checked ← IO.monoNanosNow
  match Verify.matchSpec env file with
  | .error e =>
    IO.eprintln (e.format file mmb)
    return 1
  | .ok n =>
    let done ← IO.monoNanosNow
    let ms (a b : Nat) : String := s!"{(b - a) / 1000000}.{((b - a) % 1000000) / 100000} ms"
    IO.println s!"verified: {mmb} proves the {n} statements of {mm0}"
    IO.println s!"  specification {ms start elaborated}, proofs {ms elaborated checked}, \
      matching {ms checked done}, total {ms start done}"
    return 0

def bench (path : String) : IO UInt32 :=
  if (path : System.FilePath).extension == some "mmb" then benchMmb path else benchMm0 path

def main (args : List String) : IO UInt32 := do
  match args with
  | ["dump", path] => dump path
  | ["join", path] => joinMm0 path
  | "bench" :: path :: paths =>
    let mut code : UInt32 := 0
    for p in path :: paths do
      code := max code (← bench p)
    return code
  | ["verify", path] => verifyMmb path
  | ["verify", mm0, mmb] => verifyPair mm0 mmb
  | "prove" :: _ => notImplemented "prove (phase 3)"
  | _ =>
    IO.eprintln usage
    return 2
