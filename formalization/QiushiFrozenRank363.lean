import QiushiFrozenRank363Final
import QiushiFrozenWangData

namespace QiushiMatmul.FrozenRank

theorem span363_lb17 : QuotientRankAtLeast (spanCodes [262,160,20,1]) 17 :=
  plane363RankCoverGen_lb17

theorem rep363 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 363))
      (frozenWangTable.lower 363) := by
  exact span363_lb17

end QiushiMatmul.FrozenRank
