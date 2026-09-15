import QiushiFrozenRank367Bool
import QiushiFrozenRank367Tree
import QiushiFrozenRank367Dispatch
namespace QiushiMatmul

theorem plane367RankCoverGen_lb17 :
    QuotientRankAtLeast (spanCodes [270, 160, 20, 1]) 17 :=
  generic_plane_qra plane367RankCoverGenConfig plane367RankCoverGenBool plane367RankCoverGenSourceQRA plane367RankCoverGenDeadQRA
    (by decide +kernel) plane367RankCoverGenNoModel

end QiushiMatmul
