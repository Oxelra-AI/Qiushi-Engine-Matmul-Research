import QiushiFrozenRank109

open QiushiMatmul QiushiMatmul.FrozenRank BigOperators

example : QuotientRankAtLeast (spanCodes [256,84,8,2,1]) 14 := span109_lb14

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 109))
    (frozenWangTable.lower 109) := rep109

example (i : Fin 12) : QuotientRankAtLeast (spanCodes (sources109 i)) (lower109 i) :=
  sources109_rank i

example (r : Nat) (hr : r < 14) (hlower : ∀ i, lower109 i ≤ r) :
    (∑ i : Fin 12, (r - lower109 i)) < r := capacity109 r hr hlower

example : ∀ c : Fin 512, ∃ i : Fin 12,
    spanContainsCode (sources109 i) c.val = true := sources109_cover

/-- info: 'QiushiMatmul.FrozenRank.sources109_rank' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sources109_rank

/-- info: 'QiushiMatmul.FrozenRank.span109_lb14' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms span109_lb14

/-- info: 'QiushiMatmul.FrozenRank.rep109' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rep109
