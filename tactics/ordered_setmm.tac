-- ordered, in set.mm's notation, which is prefix: a < b is `wbr a b clt`, a <= b `wbr a b cle`
-- (DESIGN.md, "The tactics system", `order`: the cheap version, a scoped search by `at`).
ordered_setmm(close=10, open=1, upto=1, penalty=2, width=5, value=0, size=2000, depth=3) =
  seq(
    bfs(filter=premises(0), depth=1),
    first(
      at($ wbr _ _ clt $, bfs(filter=or(premises(0), goal($ wbr _ _ clt $), goal($ wbr _ _ cle $)), size=@size), depth=@depth),
      at($ wbr _ _ cle $, bfs(filter=or(premises(0), goal($ wbr _ _ clt $), goal($ wbr _ _ cle $)), size=@size), depth=@depth),
      follow(subproofs(@close, rank=reach, open=0), at=open, upto=@upto, ground=true),
      follow(subproofs(@open, rank=recent), at=root),
      search(depth(follow, penalty=@penalty, by=model, width=@width, value=@value))))
