import QiushiFrozenRank368Final
import QiushiFrozenWangData

namespace QiushiMatmul.FrozenRank

theorem span368_lb17 : QuotientRankAtLeast (spanCodes [322,160,20,1]) 17 :=
  plane368RankCoverGen_lb17

theorem rep368 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 368))
      (frozenWangTable.lower 368) := by
  exact span368_lb17

end QiushiMatmul.FrozenRank
