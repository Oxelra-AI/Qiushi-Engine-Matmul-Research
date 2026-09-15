import QiushiFrozenRank361Bool
import QiushiFrozenRank361Tree
import QiushiFrozenRank361Dispatch
namespace QiushiMatmul

theorem plane361RankCoverGen_lb17 :
    QuotientRankAtLeast (spanCodes [298, 100, 20, 1]) 17 :=
  generic_plane_qra plane361RankCoverGenConfig plane361RankCoverGenBool plane361RankCoverGenSourceQRA plane361RankCoverGenDeadQRA
    (by decide +kernel) plane361RankCoverGenNoModel

end QiushiMatmul
