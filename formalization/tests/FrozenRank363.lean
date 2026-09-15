import QiushiFrozenRank363

open QiushiMatmul QiushiMatmul.FrozenRank

example : QuotientRankAtLeast (spanCodes [262,160,20,1]) 17 := span363_lb17

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 363))
    (frozenWangTable.lower 363) := rep363

example : PlaneExtBool plane363RankCoverGenConfig := plane363RankCoverGenBool

example (x : Fin 19 → Int)
    (hroot : plane363RankCoverGenOccSys.RootHolds x) : False :=
  plane363RankCoverGenNoModel x hroot

/-- info: 'QiushiMatmul.plane363RankCoverGenSourceQRA' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.plane363RankCoverGenSourceQRA

/-- info: 'QiushiMatmul.plane363RankCoverGen_lb17' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.plane363RankCoverGen_lb17

/-- info: 'QiushiMatmul.FrozenRank.span363_lb17' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.FrozenRank.span363_lb17

/-- info: 'QiushiMatmul.FrozenRank.rep363' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.FrozenRank.rep363
