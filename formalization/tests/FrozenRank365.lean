import QiushiFrozenRank365

open QiushiMatmul QiushiMatmul.FrozenRank

example : QuotientRankAtLeast (spanCodes [266,160,20,1]) 17 := span365_lb17

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 365))
    (frozenWangTable.lower 365) := rep365

example : PlaneExtBool plane365RankCoverGenConfig := plane365RankCoverGenBool

example (x : Fin 23 → Int)
    (hroot : plane365RankCoverGenOccSys.RootHolds x) : False :=
  plane365RankCoverGenNoModel x hroot

/-- info: 'QiushiMatmul.plane365RankCoverGenSourceQRA' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.plane365RankCoverGenSourceQRA

/-- info: 'QiushiMatmul.plane365RankCoverGen_lb17' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.plane365RankCoverGen_lb17

/-- info: 'QiushiMatmul.FrozenRank.span365_lb17' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.FrozenRank.span365_lb17

/-- info: 'QiushiMatmul.FrozenRank.rep365' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.FrozenRank.rep365
