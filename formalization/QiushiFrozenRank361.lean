import QiushiFrozenRank361Final
import QiushiFrozenWangData

namespace QiushiMatmul.FrozenRank

theorem span361_lb17 : QuotientRankAtLeast (spanCodes [298,100,20,1]) 17 :=
  plane361RankCoverGen_lb17

theorem rep361 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 361))
      (frozenWangTable.lower 361) := by
  exact span361_lb17

end QiushiMatmul.FrozenRank
