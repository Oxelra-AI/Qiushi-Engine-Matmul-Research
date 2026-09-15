import QiushiFrozenRank359

open QiushiMatmul QiushiMatmul.FrozenRank BigOperators

example : QuotientRankAtLeast (spanCodes [424,96,20,1]) 17 := span359_lb17

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 359))
    (frozenWangTable.lower 359) := rep359

example (i : Fin 11) : QuotientRankAtLeast (spanCodes (sources359 i)) (lower359 i) :=
  sources359_rank i

example (r : Nat) (hr : r < 17) (hlower : ∀ i, lower359 i ≤ r) :
    (∑ i : Fin 11, (r - lower359 i)) < r := capacity359 r hr hlower

example : ∀ c : Fin 512, ∃ i : Fin 11,
    spanContainsCode (sources359 i) c.val = true := sources359_cover

/-- info: 'QiushiMatmul.FrozenRank.sources359_rank' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sources359_rank

/-- info: 'QiushiMatmul.FrozenRank.span359_lb17' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms span359_lb17

/-- info: 'QiushiMatmul.FrozenRank.rep359' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rep359
