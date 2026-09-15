import QiushiFrozenRank369Final
import QiushiFrozenWangData

namespace QiushiMatmul.FrozenRank

theorem span369_lb17 : QuotientRankAtLeast (spanCodes [326,160,20,1]) 17 :=
  plane369RankCoverGen_lb17

theorem rep369 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 369))
      (frozenWangTable.lower 369) := by
  exact span369_lb17

end QiushiMatmul.FrozenRank
