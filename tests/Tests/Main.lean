import Tests.Mm0.Parser
import Tests.Mm0.Load
import Tests.Mm0.Elab
import Tests.Mm0.Corpus
import Tests.Mm0.Pairs
import Tests.Mmb.Reader
import Tests.Mmb.Corpus
import Tests.Verify.Proofs
import Tests.Verify.Spec
import Tests.Verify.Cases
import Tests.Verify.Corpus
import Tests.Prove.Subst
import Tests.Prove.Unify
import Tests.Prove.Index
import Tests.Prove.Engine

def main : IO UInt32 := do
  let ((), stats) ← (do
    Tests.Mm0.parserTests
    Tests.Mm0.loadTests
    Tests.Mm0.elabTests
    Tests.Mmb.readerTests
    Tests.Verify.proofTests
    Tests.Verify.specTests
    Tests.Verify.caseTests
    Tests.Prove.substTests
    Tests.Prove.unifyTests
    Tests.Prove.indexTests
    Tests.Prove.engineTests
    Tests.Mm0.corpusTests
    Tests.Mmb.corpusTests
    Tests.Verify.corpusTests
    Tests.Mm0.pairTests
    Tests.Prove.replayCorpusTests : Tests.TestM Unit).run {}
  IO.println s!"{stats.passed} passed, {stats.failed} failed, {stats.skipped} skipped"
  return if stats.failed == 0 then 0 else 1
