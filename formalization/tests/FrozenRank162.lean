import QiushiFrozenRank162

open QiushiMatmul QiushiMatmul.FrozenRank BigOperators

example : QuotientRankAtLeast (spanCodes [128,96,20,10,1]) 16 := span162_lb16

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 162))
    (frozenWangTable.lower 162) := rep162

example (i : Fin 7) : QuotientRankAtLeast (spanCodes (sources162 i)) (lower162 i) :=
  sources162_rank i

example (r : Nat) (hr : r < 16) (hlower : ∀ i, lower162 i ≤ r) :
    (∑ i : Fin 7, (r - lower162 i)) < r := capacity162 r hr hlower

example : ∀ c : Fin 512, ∃ i : Fin 7,
    spanContainsCode (sources162 i) c.val = true := sources162_cover

/-- info: 'QiushiMatmul.FrozenRank.sources162_rank' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sources162_rank

/-- info: 'QiushiMatmul.FrozenRank.span162_lb16' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms span162_lb16

/-- info: 'QiushiMatmul.FrozenRank.rep162' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rep162
