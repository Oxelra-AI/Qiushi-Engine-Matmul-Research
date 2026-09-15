import QiushiFrozenRank27
import QiushiFrozenRank28

open QiushiMatmul QiushiMatmul.FrozenRank

example : QuotientRankAtLeast (spanCodes [304,160,8,4,2,1]) 11 := span027_lb11
example : QuotientRankAtLeast (spanCodes [280,160,80,4,2,1]) 11 := span028_lb11

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 27))
    (frozenWangTable.lower 27) := rep027
example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 28))
    (frozenWangTable.lower 28) := rep028

example (i : Fin 7) : QuotientRankAtLeast (spanCodes (sources027 i)) 9 := sources027_rank i
example (i : Fin 7) : QuotientRankAtLeast (spanCodes (sources028 i)) 9 := sources028_rank i

/-- info: 'QiushiMatmul.FrozenRank.sources027_rank' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sources027_rank

/-- info: 'QiushiMatmul.FrozenRank.sources028_rank' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sources028_rank

/-- info: 'QiushiMatmul.FrozenRank.span027_lb11' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms span027_lb11

/-- info: 'QiushiMatmul.FrozenRank.span028_lb11' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms span028_lb11

/-- info: 'QiushiMatmul.FrozenRank.rep027' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rep027

/-- info: 'QiushiMatmul.FrozenRank.rep028' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rep028
