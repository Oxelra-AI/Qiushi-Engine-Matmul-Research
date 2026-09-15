import QiushiFrozenRank365Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane365RankCoverGenSource0050 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 32, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (128, 9), (66, 108), (32, 2), (18, 54), (10, 180), (6, 32), (1, 288)]
    (codeMat 84) (codeMat 94) (codeMat 500) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_3

theorem plane365RankCoverGenSource0051 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 34, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 63), (130, 40), (66, 464), (34, 11), (18, 8), (10, 208), (6, 2), (1, 128)]
    (codeMat 395) (codeMat 116) (codeMat 92) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
