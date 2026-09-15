import QiushiFrozenRank369

open QiushiMatmul QiushiMatmul.FrozenRank

example : QuotientRankAtLeast (spanCodes [326,160,20,1]) 17 := span369_lb17

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 369))
    (frozenWangTable.lower 369) := rep369

example : PlaneExtBool plane369RankCoverGenConfig := plane369RankCoverGenBool

example (x : Fin 23 → Int)
    (hroot : plane369RankCoverGenOccSys.RootHolds x) : False :=
  plane369RankCoverGenNoModel x hroot

/-- info: 'QiushiMatmul.plane369RankCoverGenSourceQRA' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.plane369RankCoverGenSourceQRA

/-- info: 'QiushiMatmul.plane369RankCoverGen_lb17' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.plane369RankCoverGen_lb17

/-- info: 'QiushiMatmul.FrozenRank.span369_lb17' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.FrozenRank.span369_lb17

/-- info: 'QiushiMatmul.FrozenRank.rep369' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QiushiMatmul.FrozenRank.rep369
