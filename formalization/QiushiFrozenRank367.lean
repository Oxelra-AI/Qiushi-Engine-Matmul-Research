import QiushiFrozenRank367Final
import QiushiFrozenWangData

namespace QiushiMatmul.FrozenRank

theorem span367_lb17 : QuotientRankAtLeast (spanCodes [270,160,20,1]) 17 :=
  plane367RankCoverGen_lb17

theorem rep367 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 367))
      (frozenWangTable.lower 367) := by
  exact span367_lb17

end QiushiMatmul.FrozenRank
