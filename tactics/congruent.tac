-- learned, with the congruence procedure (DESIGN.md, "The tactics system"): at every open
-- goal L = R or L <-> R (or ph -> L = R) whose sides are applications of one term, the
-- file's congruence lemmas are followed down to where the sides differ, before the rails
-- and the search; also at the goals the rails leave open (chain). Its steps cost nothing.
congruent(close=10, open=1, upto=1, penalty=2, width=5, value=0) =
  seq(
    bfs(filter=premises(0), depth=1),
    first(
      follow(congr, at=open, chain=true),
      follow(subproofs(@close, rank=reach, open=0), at=open, upto=@upto, ground=true),
      follow(subproofs(@open, rank=recent), at=root),
      search(depth(follow, penalty=@penalty, by=model, width=@width, value=@value))))
