import QiushiFrozenRank33

open QiushiMatmul QiushiMatmul.FrozenRank BigOperators

example : QuotientRankAtLeast (spanCodes [160,68,20,8,2,1]) 14 := span033_lb14

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 33))
    (frozenWangTable.lower 33) := rep033

example (i : Fin 7) : QuotientRankAtLeast (spanCodes (sources033 i)) (lower033 i) :=
  sources033_rank i

example (r : Nat) (hr : r < 14) (hlower : ∀ i, lower033 i ≤ r) :
    (∑ i : Fin 7, (r - lower033 i)) < r := capacity033 r hr hlower

example : ∀ c : Fin 512, ∃ i : Fin 7,
    spanContainsCode (sources033 i) c.val = true := sources033_cover

/-- info: 'QiushiMatmul.FrozenRank.sources033_rank' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sources033_rank

/-- info: 'QiushiMatmul.FrozenRank.span033_lb14' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms span033_lb14

/-- info: 'QiushiMatmul.FrozenRank.rep033' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rep033
