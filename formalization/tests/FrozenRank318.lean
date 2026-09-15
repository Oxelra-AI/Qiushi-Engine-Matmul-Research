import QiushiFrozenRank318

open QiushiMatmul QiushiMatmul.FrozenRank BigOperators

example : QuotientRankAtLeast (spanCodes [290,160,10,1]) 17 := span318_lb17

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 318))
    (frozenWangTable.lower 318) := rep318

example (i : Fin 8) : QuotientRankAtLeast (spanCodes (sources318 i)) (lower318 i) :=
  sources318_rank i

example (r : Nat) (hr : r < 17) (hlower : ∀ i, lower318 i ≤ r) :
    (∑ i : Fin 8, (r - lower318 i)) < r := capacity318 r hr hlower

example : ∀ c : Fin 512, ∃ i : Fin 8,
    spanContainsCode (sources318 i) c.val = true := sources318_cover

/-- info: 'QiushiMatmul.FrozenRank.sources318_rank' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sources318_rank

/-- info: 'QiushiMatmul.FrozenRank.span318_lb17' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms span318_lb17

/-- info: 'QiushiMatmul.FrozenRank.rep318' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rep318
