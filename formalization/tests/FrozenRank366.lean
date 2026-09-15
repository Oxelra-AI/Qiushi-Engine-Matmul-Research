import QiushiFrozenRank366

open QiushiMatmul QiushiMatmul.FrozenRank BigOperators

example : QuotientRankAtLeast (spanCodes [268,160,20,1]) 17 := span366_lb17

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 366))
    (frozenWangTable.lower 366) := rep366

example (i : Fin 13) : QuotientRankAtLeast (spanCodes (sources366 i)) (lower366 i) :=
  sources366_rank i

example (r : Nat) (hr : r < 17) (hlower : ∀ i, lower366 i ≤ r) :
    (∑ i : Fin 13, (r - lower366 i)) < r := capacity366 r hr hlower

example : ∀ c : Fin 512, ∃ i : Fin 13,
    spanContainsCode (sources366 i) c.val = true := sources366_cover

/-- info: 'QiushiMatmul.FrozenRank.sources366_rank' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sources366_rank

/-- info: 'QiushiMatmul.FrozenRank.span366_lb17' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms span366_lb17

/-- info: 'QiushiMatmul.FrozenRank.rep366' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rep366
