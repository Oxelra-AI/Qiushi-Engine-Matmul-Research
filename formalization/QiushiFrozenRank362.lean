import QiushiFrozenRank362Final
import QiushiFrozenWangData

namespace QiushiMatmul.FrozenRank

theorem span362_lb17 : QuotientRankAtLeast (spanCodes [296,102,20,1]) 17 :=
  plane362RankCoverGen_lb17

theorem rep362 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 362))
      (frozenWangTable.lower 362) := by
  exact span362_lb17

end QiushiMatmul.FrozenRank
