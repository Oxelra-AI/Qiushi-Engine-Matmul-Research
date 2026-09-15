import QiushiFrozenRank362

open QiushiMatmul QiushiMatmul.FrozenRank

example : QuotientRankAtLeast (spanCodes [296,102,20,1]) 17 := span362_lb17

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 362))
    (frozenWangTable.lower 362) := rep362

example : PlaneExtBool plane362RankCoverGenConfig := plane362RankCoverGenBool

example (x : Fin 24 → Int)
    (hroot : plane362RankCoverGenOccSys.RootHolds x) : False :=
  plane362RankCoverGenNoModel x hroot

/-- info: 'QiushiMatmul.plane362RankCoverGenSourceQRA' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.plane362RankCoverGenSourceQRA

/-- info: 'QiushiMatmul.plane362RankCoverGen_lb17' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.plane362RankCoverGen_lb17

/-- info: 'QiushiMatmul.FrozenRank.span362_lb17' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.FrozenRank.span362_lb17

/-- info: 'QiushiMatmul.FrozenRank.rep362' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.FrozenRank.rep362
