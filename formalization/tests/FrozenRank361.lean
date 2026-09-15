import QiushiFrozenRank361

open QiushiMatmul QiushiMatmul.FrozenRank

example : QuotientRankAtLeast (spanCodes [298,100,20,1]) 17 := span361_lb17

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 361))
    (frozenWangTable.lower 361) := rep361

example : PlaneExtBool plane361RankCoverGenConfig := plane361RankCoverGenBool

example (x : Fin 24 → Int)
    (hroot : plane361RankCoverGenOccSys.RootHolds x) : False :=
  plane361RankCoverGenNoModel x hroot

/-- info: 'QiushiMatmul.plane361RankCoverGenSourceQRA' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.plane361RankCoverGenSourceQRA

/-- info: 'QiushiMatmul.plane361RankCoverGen_lb17' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.plane361RankCoverGen_lb17

/-- info: 'QiushiMatmul.FrozenRank.span361_lb17' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.FrozenRank.span361_lb17

/-- info: 'QiushiMatmul.FrozenRank.rep361' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.FrozenRank.rep361
