-- The replay of subproofs combined with breadth-first search, by cost: a step that the
-- replay takes costs nothing, one that the search takes costs one, and each round expands
-- the leaves of the least cost. Subproofs go down at the goals of cost upto or less (with
-- ground, only those without metavariables), count at each, chosen and ranked as
-- `subproofs` says, but not at a goal that a subproof left open; such a goal costs penalty
-- more. Without subproofs, breadth-first round for round.
rails(count=3, rank=occurrences, min=2, source=earlier, upto=0, ground=true, penalty=0, open=1000000) =
  first(
    follow(subproofs(@count, rank=@rank, min=@min, source=@source, open=@open),
           at=open, upto=@upto, ground=@ground),
    search(depth(follow, penalty=@penalty)))
