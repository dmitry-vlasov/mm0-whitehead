/-
`lake exe ref-search <file.mmb> <theorem> <rounds>`: the reference engine on a theorem
of a proof file, breadth first for the given number of rounds; prints the nodes and
every proof at the root.
-/
import Whitehead
import Theory
import Theory.Convert

open Theory

def main (args : List String) : IO UInt32 := do
  let keyed := args.contains "--keyed"
  match args.filter (· != "--keyed") with
  | [path, thm, rounds] =>
    let file ←
      match Whitehead.Mmb.MmbFile.parse (← IO.FS.readBinFile path) with
      | .ok f => pure f
      | .error e =>
        IO.eprintln (e.format path)
        return 1
    let db ←
      match Whitehead.Prove.Db.ofFile file with
      | .ok d => pure d
      | .error m =>
        IO.eprintln s!"{path}: {m}"
        return 1
    let some idx := (db.asserts.findIdx? (·.name == thm)) <|> thm.toNat?
      | IO.eprintln s!"{path}: no theorem {thm}"
        return 1
    let task := db.task idx
    let (dbm, names) := Convert.database db task
    let st := Convert.statement db task
    let terms := db.terms.map (·.name)
    let n := rounds.toNat!
    let start ← IO.monoMsNow
    let s := State.run Unify.postulate dbm st n
    let root := s.rootEntries Unify.postulate st
    let done ← IO.monoMsNow
    IO.println s!"{path}: {db.asserts[idx]!.name}, {dbm.asserts.length} assertions, {n} rounds: \
      {s.enodes.size} expression nodes, {s.anodes.size} assertion nodes, \
      {root.length} proofs at the root, in {done - start} ms"
    IO.println s!"  goal {Convert.expText terms st.concl}; hypotheses {st.hyps.map (Convert.expText terms)}"
    for E in root do
      IO.println s!"  {Convert.proofText names terms (E.proof dbm s)}"
    if keyed then
      let start ← IO.monoMsNow
      let kroot := keyedRoot Unify.postulate st s
      let done ← IO.monoMsNow
      IO.println s!"  keyed: {kroot.length} entries at the root, one per key, in {done - start} ms"
      for K in kroot do
        IO.println s!"  {Convert.proofText names terms (K.proof dbm s)} with \
          {Convert.expText terms (K.sub.apply st.concl)}, {K.conds.length} pending"
    return 0
  | _ =>
    IO.eprintln "usage: ref-search <file.mmb> <theorem> <rounds> [--keyed]"
    return 2
