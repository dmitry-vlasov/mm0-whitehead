/-
Tests of the chain miner on `tests/fixtures/prove/logic.mmb`: the counts by length,
the most frequent chain, and the coverage, pinned from a run that was read by hand.
-/
import Whitehead.Prove.Chains
import Tests.Harness

open Whitehead.Mmb Whitehead.Prove

namespace Tests.Prove

def chainTests : TestM Unit := do
  let path : System.FilePath := "tests/fixtures/prove/logic.mmb"
  let file ←
    match MmbFile.parse (← IO.FS.readBinFile path) with
    | .ok f => pure f
    | .error e => check "chains: the fixture is read" false e.msg; return
  let db ←
    match Db.ofFile file with
    | .ok db => pure db
    | .error msg => check "chains: the fixture becomes a database" false msg; return
  -- every chain kept: the counts are those of all chains
  match mineChains db { maxLen := 6, min := 1, top := 3 } with
  | .error msg => check "chains: mined" false msg
  | .ok s =>
    checkEq "chains: proofs and steps" (s.proofs, s.steps) (16, 61)
    checkEq "chains: lengths mined" (s.lengths.map (·.len)) #[2, 3, 4, 5, 6]
    let l2 := s.lengths[0]!
    checkEq "chains of 2: occurrences, all counted" (l2.occurrences, l2.counted) (45, 45)
    checkEq "chains of 2: to the root, from a hypothesis" (l2.toRoot, l2.fromHyp) (23, 6)
    checkEq "chains of 2: distinct" l2.frequent 37
    let (key, n, proofs) := l2.top[0]!
    checkEq "chains of 2: the most frequent" (chainText db key, n) ("syl .0 ax_3", 3)
    check "chains of 2: the most frequent occurs in one to three proofs" (1 ≤ proofs && proofs ≤ 3) s!"{proofs}"
    checkEq "chains of 6: occurrences" s.lengths[4]!.occurrences 9
    -- a step with k - 1 ancestors ends a chain of length k: the occurrences fall with k
    check "chains: occurrences fall with the length"
      (s.lengths.zip (s.lengths.extract 1 s.lengths.size) |>.all fun (a, b) => a.occurrences ≥ b.occurrences)
    checkEq "chains: coverage at 2, 10, 100, 1000" s.covered #[(2, 27), (10, 0), (100, 0), (1000, 0)]
  -- with the default minimum the frequent chains are those that occur twice, and the
  -- chains of 3 are counted only under a frequent chain of 2
  match mineChains db { maxLen := 3, min := 2 } with
  | .error msg => check "chains: mined with a minimum" false msg
  | .ok s =>
    check "chains with a minimum: fewer frequent chains of 2, and the frequent ones occur twice"
      (s.lengths[0]!.frequent < 37 && s.lengths[0]!.top.all (·.2.1 ≥ 2)) s!"{s.lengths[0]!.frequent}"
    check "chains with a minimum: chains of 3 counted only under a frequent chain of 2"
      (s.lengths[1]!.counted < s.lengths[1]!.occurrences) s!"{s.lengths[1]!.counted} of {s.lengths[1]!.occurrences}"
    checkEq "chains with a minimum: the same coverage at 2" s.covered[0]! (2, 27)

end Tests.Prove
