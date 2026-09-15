import QiushiFrozenRank368

open QiushiMatmul QiushiMatmul.FrozenRank

example : QuotientRankAtLeast (spanCodes [322,160,20,1]) 17 := span368_lb17

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 368))
    (frozenWangTable.lower 368) := rep368

example : PlaneExtBool plane368RankCoverGenConfig := plane368RankCoverGenBool

example (x : Fin 20 → Int)
    (hroot : plane368RankCoverGenOccSys.RootHolds x) : False :=
  plane368RankCoverGenNoModel x hroot

/-- info: 'QiushiMatmul.plane368RankCoverGenSourceQRA' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.plane368RankCoverGenSourceQRA

/-- info: 'QiushiMatmul.plane368RankCoverGen_lb17' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.plane368RankCoverGen_lb17

/-- info: 'QiushiMatmul.FrozenRank.span368_lb17' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.FrozenRank.span368_lb17

/-- info: 'QiushiMatmul.FrozenRank.rep368' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.FrozenRank.rep368
