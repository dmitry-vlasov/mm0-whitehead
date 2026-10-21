-- congruent, with the ring procedure first (DESIGN.md, "The tactics system", "ring"): at
-- every open goal L = R (or ph -> L = R) over the file's ring operations, both sides are
-- normalized by the file's own lemmas, the closure side goals planned down to the atoms;
-- then congruence, the rails and the search. The procedures' steps cost nothing.
arith(close=10, open=1, upto=1, penalty=2, width=5, value=0) =
  seq(
    bfs(filter=premises(0), depth=1),
    first(
      follow(ring, at=open, chain=true),
      follow(congr, at=open, chain=true),
      follow(subproofs(@close, rank=reach, open=0), at=open, upto=@upto, ground=true),
      follow(subproofs(@open, rank=recent), at=root),
      search(depth(follow, penalty=@penalty, by=model, width=@width, value=@value))))
