import QiushiFrozenRank24

open QiushiMatmul QiushiMatmul.FrozenRank

example : QuotientRankAtLeast (spanCodes [160,80,8,4,2,1]) 11 := span024_lb11

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 24))
    (frozenWangTable.lower 24) := rep024

example (i : Fin 7) : QuotientRankAtLeast (spanCodes (sources024 i)) 9 :=
  sources024_rank i

example : ∀ c : Fin 512, ∃ i : Fin 7,
    spanContainsCode (sources024 i) c.val = true := sources024_cover

/-- info: 'QiushiMatmul.FrozenRank.sources024_rank' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sources024_rank

/-- info: 'QiushiMatmul.FrozenRank.span024_lb11' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms span024_lb11

/-- info: 'QiushiMatmul.FrozenRank.rep024' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rep024
