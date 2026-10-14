/-
`lake exe certify <file.mmb> [<spec.mm0>]`: the verified checker on a proof file, for
instance one the prover wrote (`prove replay|search … -o file.mmb`). The prover's
proofs are then sound by the theorems of the verifier's verification
(`docs/VERIFIER-THEORY.md`), not by trust in the prover or the fast verifier:

- `checkFile` accepts the decoded file: by `Verifier.file_valid` (through
  `checkFile_sound`) the environment it declares is well-formed and every theorem of it
  is proved (`env.ok`, `env.proof'` of the MM0 semantics);
- with a specification, `extendRev` matches the file to it: by `Verifier.spec_valid`,
  `mm0.mm0`'s `ValidEnv` of the specification, but for the specification's own
  well-formedness, which the front end establishes.

Trusted: Lean's kernel and compiler, the port of the semantics, the byte reader, the
`.mm0` front end, and the two conversions (`Verifier/OfMmb.lean`, `Verifier/OfMm0.lean`).
-/
import Verifier.OfMm0
import Whitehead.Mm0.Load
import Whitehead.Mm0.Elab

open Whitehead

def main (args : List String) : IO UInt32 := do
  let some path := args.find? (·.endsWith ".mmb")
    | IO.eprintln "usage: certify <file.mmb> [<spec.mm0>]"; return 2
  let t0 ← IO.monoMsNow
  let file ← match Mmb.MmbFile.parse (← IO.FS.readBinFile path) with
    | .ok f => pure f
    | .error e => IO.eprintln (e.format path); return 1
  let vf ← match Verifier.fileOf file with
    | .ok vf => pure vf
    | .error m => IO.eprintln s!"{path}: not certified: a stream does not decode: {m}"; return 1
  if !Verifier.checkFile vf then
    match Verifier.firstFailure vf with
    | some i => IO.eprintln s!"{path}: not certified: the verified checker rejects statement {i}"
    | none => IO.eprintln s!"{path}: not certified"
    return 1
  let t1 ← IO.monoMsNow
  IO.println s!"{path}: certified ({vf.stmts.length} statements, {t1 - t0} ms): the declared environment is \
    well-formed and every theorem of it is proved (file_valid)"
  if let some specPath := args.find? (·.endsWith ".mm0") then
    let env ← match ← Mm0.load specPath with
      | .error e => IO.eprintln e.format; return 1
      | .ok spec => match Mm0.elaborate spec with
        | .error e => IO.eprintln e.format; return 1
        | .ok env => pure env
    let some E := Verifier.toEnv vf
      | IO.eprintln s!"{path}: not certified: the environment does not decode"; return 1
    let S := Verifier.specEnv env (Verifier.termMapOf file)
    if Verifier.extendRev S.reverse E.reverse (Verifier.localFlags file).reverse then
      IO.println s!"{specPath}: proved by {path} (spec_valid: ValidEnv but for the specification's own well-formedness)"
    else
      IO.eprintln s!"{specPath}: not certified: {path} does not extend the specification"
      return 1
  return 0
