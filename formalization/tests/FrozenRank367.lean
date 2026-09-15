import QiushiFrozenRank367

open QiushiMatmul QiushiMatmul.FrozenRank

example : QuotientRankAtLeast (spanCodes [270,160,20,1]) 17 := span367_lb17

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 367))
    (frozenWangTable.lower 367) := rep367

example : PlaneExtBool plane367RankCoverGenConfig := plane367RankCoverGenBool

example (x : Fin 24 → Int)
    (hroot : plane367RankCoverGenOccSys.RootHolds x) : False :=
  plane367RankCoverGenNoModel x hroot

/-- info: 'QiushiMatmul.plane367RankCoverGenSourceQRA' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.plane367RankCoverGenSourceQRA

/-- info: 'QiushiMatmul.plane367RankCoverGen_lb17' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.plane367RankCoverGen_lb17

/-- info: 'QiushiMatmul.FrozenRank.span367_lb17' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.FrozenRank.span367_lb17

/-- info: 'QiushiMatmul.FrozenRank.rep367' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.FrozenRank.rep367
