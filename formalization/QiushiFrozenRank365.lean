import QiushiFrozenRank365Final
import QiushiFrozenWangData

namespace QiushiMatmul.FrozenRank

theorem span365_lb17 : QuotientRankAtLeast (spanCodes [266,160,20,1]) 17 :=
  plane365RankCoverGen_lb17

theorem rep365 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 365))
      (frozenWangTable.lower 365) := by
  exact span365_lb17

end QiushiMatmul.FrozenRank
