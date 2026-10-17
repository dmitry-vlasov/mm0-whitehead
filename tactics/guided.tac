-- Breadth-first search guided by the subproofs of earlier proofs: at the root and at the
-- goals of the first round, the subproofs that leave nothing open (close of them, ranked
-- by reach); at the root, the open subproofs of the latest proofs (open of them, ranked by
-- recent); the steps they take cost nothing, and a goal one of them leaves open costs
-- penalty more. The best measured on set.mm (DESIGN.md, "Ranks for the rails").
guided(close=10, open=1, upto=1, penalty=2) =
  first(
    follow(subproofs(@close, rank=reach, open=0), at=open, upto=@upto, ground=true),
    follow(subproofs(@open, rank=recent), at=root),
    search(depth(follow, penalty=@penalty)))
