import QiushiFrozenRank362Bool
import QiushiFrozenRank362Tree
import QiushiFrozenRank362Dispatch
namespace QiushiMatmul

theorem plane362RankCoverGen_lb17 :
    QuotientRankAtLeast (spanCodes [296, 102, 20, 1]) 17 :=
  generic_plane_qra plane362RankCoverGenConfig plane362RankCoverGenBool plane362RankCoverGenSourceQRA plane362RankCoverGenDeadQRA
    (by decide +kernel) plane362RankCoverGenNoModel

end QiushiMatmul
