-- learned, with a sub-search at every order goal first: at a goal x < y or x <= y, breadth
-- first among the variants whose new goals are order facts or none, to depth 3 below the
-- goal and 2,000 nodes (DESIGN.md, "The tactics system", `order`: the cheap version, a
-- scoped search by `at`, before a procedure).
ordered(close=10, open=1, upto=1, penalty=2, width=5, value=0, size=2000, depth=3) =
  seq(
    bfs(filter=premises(0), depth=1),
    first(
      at($ _ < _ $, bfs(filter=or(premises(0), goal($ _ < _ $), goal($ _ <_ _ $)), size=@size), depth=@depth),
      at($ _ <_ _ $, bfs(filter=or(premises(0), goal($ _ < _ $), goal($ _ <_ _ $)), size=@size), depth=@depth),
      follow(subproofs(@close, rank=reach, open=0), at=open, upto=@upto, ground=true),
      follow(subproofs(@open, rank=recent), at=root),
      search(depth(follow, penalty=@penalty, by=model, width=@width, value=@value))))
