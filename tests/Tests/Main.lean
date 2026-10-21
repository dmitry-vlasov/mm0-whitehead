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
import Tests.Prove.Prod
import Tests.Prove.Engine
import Tests.Prove.Defs
import Tests.Prove.Chains
import Tests.Prove.Session
import Tests.Prove.Filter
import Tests.Prove.Hints
import Tests.Prove.Rails
import Tests.Prove.Congr
import Tests.Prove.Ring
import Tests.Prove.Tactics
import Tests.Prove.Mm1
import Tests.Prove.Dataset
import Tests.Mcp

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
    Tests.Prove.prodTests
    Tests.Prove.engineTests
    Tests.Prove.defsTests
    Tests.Prove.chainTests
    Tests.Prove.sessionTests
    Tests.Prove.sessionForwardTests
    Tests.Prove.filterTests
    Tests.Prove.dslTests
    Tests.Prove.measureTests
    Tests.Prove.usesTests
    Tests.Prove.subproofTests
    Tests.Prove.hintTests
    Tests.Prove.railsTests
    Tests.Prove.congrTests
    Tests.Prove.ringTests
    Tests.Prove.tacticsTests
    Tests.Prove.mm1Tests
    Tests.Prove.datasetTests
    Tests.Prove.modelTests
    Tests.Mcp.jsonTests
    Tests.Mcp.serverTests
    Tests.Prove.fullReplayTests
    Tests.Mm0.corpusTests
    Tests.Mmb.corpusTests
    Tests.Verify.corpusTests
    Tests.Mm0.pairTests
    Tests.Mcp.printerTests
    Tests.Prove.replayCorpusTests
    Tests.Prove.replayDefsCorpusTests : Tests.TestM Unit).run {}
  IO.println s!"{stats.passed} passed, {stats.failed} failed, {stats.skipped} skipped"
  return if stats.failed == 0 then 0 else 1
