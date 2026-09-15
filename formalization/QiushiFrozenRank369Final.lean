import QiushiFrozenRank369Bool
import QiushiFrozenRank369Tree
import QiushiFrozenRank369Dispatch
namespace QiushiMatmul

theorem plane369RankCoverGen_lb17 :
    QuotientRankAtLeast (spanCodes [326, 160, 20, 1]) 17 :=
  generic_plane_qra plane369RankCoverGenConfig plane369RankCoverGenBool plane369RankCoverGenSourceQRA plane369RankCoverGenDeadQRA
    (by decide +kernel) plane369RankCoverGenNoModel

end QiushiMatmul
