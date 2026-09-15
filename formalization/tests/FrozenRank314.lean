import QiushiFrozenRank314

open QiushiMatmul QiushiMatmul.FrozenRank BigOperators

example : QuotientRankAtLeast (spanCodes [258,160,10,1]) 17 := span314_lb17

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 314))
    (frozenWangTable.lower 314) := rep314

example (i : Fin 7) : QuotientRankAtLeast (spanCodes (sources314 i)) (lower314 i) :=
  sources314_rank i

example (r : Nat) (hr : r < 17) (hlower : ∀ i, lower314 i ≤ r) :
    (∑ i : Fin 7, (r - lower314 i)) < r := capacity314 r hr hlower

example : ∀ c : Fin 512, ∃ i : Fin 7,
    spanContainsCode (sources314 i) c.val = true := sources314_cover

/-- info: 'QiushiMatmul.FrozenRank.sources314_rank' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sources314_rank

/-- info: 'QiushiMatmul.FrozenRank.span314_lb17' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms span314_lb17

/-- info: 'QiushiMatmul.FrozenRank.rep314' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rep314
