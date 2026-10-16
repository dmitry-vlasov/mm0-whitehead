/-
How often the assertions of a file are used in its proofs: the first rank of variants
(`docs/DESIGN.md`, "Phase 4", "Filters", the rank atom).

The count of an assertion, for a theorem being proved, is the number of proofs of the
theorems before it that use the assertion; a proof counts once however often it uses it.
Only the proofs before the theorem count, so the theorem's own proof and those after it
say nothing about it: what is measured with the count is out of sample.

A proof is read as its command stream (`MmbFile.proofCmds`), in which a shared subproof
appears once. Counting proofs rather than uses is one answer to question 5 of
2026-10-13 ("uses, or proofs?"), which is still open; uses would let a subproof used
thousands of times in a few proofs (`renegcli`) count thousands of times.
-/
import Whitehead.Prove.Db

namespace Whitehead.Prove

structure Uses where
  /-- For each assertion, the theorems whose proofs use it, by their number, in order. -/
  byAssertion : Array (Array Nat) := #[]
  deriving Inhabited

namespace Uses

/-- The uses in the proofs of `f`, a file with `n` assertions. A proof that cannot be read
is left out: the verifier is what says why. -/
def ofFile (f : Mmb.MmbFile) (n : Nat) : Uses := Id.run do
  let mut by_ : Array (Array Nat) := Array.replicate n #[]
  for s in f.stmts do
    let .thm _ := s.kind | continue
    let .ok cmds := f.proofCmds s | continue
    let mut seen : Std.HashSet Nat := {}
    for c in cmds do
      if let .thm id _ := c then
        if id < n && !seen.contains id then
          seen := seen.insert id
          by_ := by_.modify id (·.push s.index)
  return { byAssertion := by_ }

/-- How many proofs of the theorems numbered below `limit` use assertion `a`. -/
def before (u : Uses) (a limit : Nat) : Nat := Id.run do
  let some ts := u.byAssertion[a]? | return 0
  -- the first place whose theorem is `limit` or after
  let mut lo := 0
  let mut hi := ts.size
  while lo < hi do
    let mid := (lo + hi) / 2
    if ts[mid]! < limit then lo := mid + 1 else hi := mid
  return lo

end Uses

end Whitehead.Prove
