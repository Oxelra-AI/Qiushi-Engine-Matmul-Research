import QiushiFrozenRank363Bool
import QiushiFrozenRank363Tree
import QiushiFrozenRank363Dispatch
namespace QiushiMatmul

theorem plane363RankCoverGen_lb17 :
    QuotientRankAtLeast (spanCodes [262, 160, 20, 1]) 17 :=
  generic_plane_qra plane363RankCoverGenConfig plane363RankCoverGenBool plane363RankCoverGenSourceQRA plane363RankCoverGenDeadQRA
    (by decide +kernel) plane363RankCoverGenNoModel

end QiushiMatmul
