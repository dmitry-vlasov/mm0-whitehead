import Whitehead

open Whitehead

def usage : String :=
  "usage: mm0-whitehead <command> [arguments]

  dump <file.mm0>                print the parsed statements of a specification file
  join <file.mm0>                print a specification with its imports included
  dump <file.mmb>                print a decoded proof file: statements and proofs
  verify <file.mm0> <file.mmb>   check a proof file against its specification  (phase 2)
  prove ...                      automated proof search                        (phase 3)
  bench <file> ...               time the .mm0 parser or the .mmb reader on the given files"

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
    {micros / 1000}.{(micros % 1000) / 100} ms, {mbPerSec} MB/s"
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
  | "verify" :: _ => notImplemented "verify (phase 2)"
  | "prove" :: _ => notImplemented "prove (phase 3)"
  | _ =>
    IO.eprintln usage
    return 2
