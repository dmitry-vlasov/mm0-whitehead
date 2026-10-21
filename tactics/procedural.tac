-- guided, with the procedures first and no learned model: at every open goal the ring
-- normalization and the congruence lemmas, then the rails, then breadth first. For a
-- file the model was not trained on (peano, where learned fills fewer gaps than bfs), and
-- for the gap filler, whose holes are short.
procedural(close=10, open=1, upto=1, penalty=2) =
  first(
    follow(ring, at=open, chain=true),
    follow(congr, at=open, chain=true),
    follow(subproofs(@close, rank=reach, open=0), at=open, upto=@upto, ground=true),
    follow(subproofs(@open, rank=recent), at=root),
    search(depth(follow, penalty=@penalty)))
