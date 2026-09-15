import QiushiFrozenRank260

open QiushiMatmul QiushiMatmul.FrozenRank BigOperators

example : QuotientRankAtLeast (spanCodes [80,12,2,1]) 16 := span260_lb16

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 260))
    (frozenWangTable.lower 260) := rep260

example (i : Fin 7) : QuotientRankAtLeast (spanCodes (sources260 i)) (lower260 i) :=
  sources260_rank i

example (r : Nat) (hr : r < 16) (hlower : ∀ i, lower260 i ≤ r) :
    (∑ i : Fin 7, (r - lower260 i)) < r := capacity260 r hr hlower

example : ∀ c : Fin 512, ∃ i : Fin 7,
    spanContainsCode (sources260 i) c.val = true := sources260_cover

/-- info: 'QiushiMatmul.FrozenRank.sources260_rank' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sources260_rank

/-- info: 'QiushiMatmul.FrozenRank.span260_lb16' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms span260_lb16

/-- info: 'QiushiMatmul.FrozenRank.rep260' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rep260
