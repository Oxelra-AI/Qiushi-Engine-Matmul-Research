import QiushiFrozenRank316

open QiushiMatmul QiushiMatmul.FrozenRank BigOperators

example : QuotientRankAtLeast (spanCodes [262,160,10,1]) 17 := span316_lb17

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 316))
    (frozenWangTable.lower 316) := rep316

example (i : Fin 7) : QuotientRankAtLeast (spanCodes (sources316 i)) (lower316 i) :=
  sources316_rank i

example (r : Nat) (hr : r < 17) (hlower : ∀ i, lower316 i ≤ r) :
    (∑ i : Fin 7, (r - lower316 i)) < r := capacity316 r hr hlower

example : ∀ c : Fin 512, ∃ i : Fin 7,
    spanContainsCode (sources316 i) c.val = true := sources316_cover

/-- info: 'QiushiMatmul.FrozenRank.sources316_rank' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sources316_rank

/-- info: 'QiushiMatmul.FrozenRank.span316_lb17' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms span316_lb17

/-- info: 'QiushiMatmul.FrozenRank.rep316' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rep316
