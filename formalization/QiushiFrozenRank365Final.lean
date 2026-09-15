import QiushiFrozenRank365Bool
import QiushiFrozenRank365Tree
import QiushiFrozenRank365Dispatch
namespace QiushiMatmul

theorem plane365RankCoverGen_lb17 :
    QuotientRankAtLeast (spanCodes [266, 160, 20, 1]) 17 :=
  generic_plane_qra plane365RankCoverGenConfig plane365RankCoverGenBool plane365RankCoverGenSourceQRA plane365RankCoverGenDeadQRA
    (by decide +kernel) plane365RankCoverGenNoModel

end QiushiMatmul
