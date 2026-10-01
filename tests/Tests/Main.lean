import Tests.Mm0.Parser
import Tests.Mm0.Corpus

def main : IO UInt32 := do
  let ((), stats) ← (do Tests.Mm0.parserTests; Tests.Mm0.corpusTests : Tests.TestM Unit).run {}
  IO.println s!"{stats.passed} passed, {stats.failed} failed, {stats.skipped} skipped"
  return if stats.failed == 0 then 0 else 1
