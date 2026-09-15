import QiushiFrozenRank362Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane362RankCoverGenSource0030 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 32, 20, 12, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 288), (128, 219), (68, 150), (32, 32), (20, 28), (12, 20), (2, 3), (1, 2)]
    (codeMat 465) (codeMat 282) (codeMat 267) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
