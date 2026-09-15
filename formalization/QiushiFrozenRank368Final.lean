import QiushiFrozenRank368Bool
import QiushiFrozenRank368Tree
import QiushiFrozenRank368Dispatch
namespace QiushiMatmul

theorem plane368RankCoverGen_lb17 :
    QuotientRankAtLeast (spanCodes [322, 160, 20, 1]) 17 :=
  generic_plane_qra plane368RankCoverGenConfig plane368RankCoverGenBool plane368RankCoverGenSourceQRA plane368RankCoverGenDeadQRA
    (by decide +kernel) plane368RankCoverGenNoModel

end QiushiMatmul
