-- guided, with the variants of a goal ordered by the learned model (--model FILE). First,
-- at the root, the variants without premises, which prove the goal at once if they apply
-- (one-step proofs that a model may rank low, as on the compiler's theorems); then the
-- closing rails at the root and the first round, the open rail of the latest proofs at
-- the root, and a search where a step costs 1 and its place among its goal's variants by
-- the model's score, divided by width (DESIGN.md, "The learned ranking layer"). With
-- value K, a step also costs K times -ln V of each of its new goals, V the learned
-- probability that a goal is proved (--value FILE), less that of its goal's best first
-- variant; with absolute=1, not less (stronger on set.mm, weaker on mm0's long chains).
learned(close=10, open=1, upto=1, penalty=2, width=5, value=0, absolute=0) =
  seq(
    bfs(filter=premises(0), depth=1),
    first(
      follow(subproofs(@close, rank=reach, open=0), at=open, upto=@upto, ground=true),
      follow(subproofs(@open, rank=recent), at=root),
      search(depth(follow, penalty=@penalty, by=model, width=@width, value=@value, absolute=@absolute))))
