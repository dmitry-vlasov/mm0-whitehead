import Whitehead

open Whitehead

def usage : String :=
  "usage: mm0-whitehead <command> [arguments]

  dump <file.mm0>                print the parsed statements of a specification file
  dump <file.mmb>                print a decoded proof file            (not implemented yet)
  verify <file.mm0> <file.mmb>   check a proof file against its specification  (phase 2)
  prove ...                      automated proof search                        (phase 3)
  bench <file.mm0> ...           time the .mm0 parser on the given files"

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

def dump (path : String) : IO UInt32 :=
  match (path : System.FilePath).extension with
  | some "mm0" => dumpMm0 path
  | some "mmb" => notImplemented "dump of .mmb files (the reader follows docs/MMB-NOTES.md)"
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

def main (args : List String) : IO UInt32 := do
  match args with
  | ["dump", path] => dump path
  | "bench" :: path :: paths =>
    let mut code : UInt32 := 0
    for p in path :: paths do
      code := max code (← benchMm0 p)
    return code
  | "verify" :: _ => notImplemented "verify (phase 2)"
  | "prove" :: _ => notImplemented "prove (phase 3)"
  | _ =>
    IO.eprintln usage
    return 2
