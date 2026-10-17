-- Subproofs of earlier proofs put down at goals and followed step by step: count at a
-- goal, chosen and ranked as `subproofs` says; at open (every open goal, each once, also
-- those that a subproof left open) or root. Unbounded alone: within limited or a time.
replay(count=3, rank=occurrences, min=2, source=earlier, at=open, open=1000000) =
  follow(subproofs(@count, rank=@rank, min=@min, source=@source, open=@open), at=@at, chain=true)
