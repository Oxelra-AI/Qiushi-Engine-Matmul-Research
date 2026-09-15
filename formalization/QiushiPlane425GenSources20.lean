import QiushiPlane425GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane425GenSource0200 :
    QuotientRankAtLeast (spanCodes [256, 144, 80, 32, 8, 4, 2, 1]) 6 := by
  apply quotientRankAtLeast_weaken (n := 6) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 64, 16, 8, 4, 2, 1] [(256, 8), (144, 432), (80, 416), (32, 64), (8, 256), (4, 1), (2, 6), (1, 4)]
    (codeMat 161) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_2

theorem plane425GenSource0201 :
    QuotientRankAtLeast (spanCodes [256, 144, 80, 48, 8, 4, 2, 1]) 6 := by
  apply quotientRankAtLeast_weaken (n := 6) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 64, 16, 8, 4, 2, 1] [(256, 16), (144, 432), (80, 424), (48, 256), (8, 320), (4, 2), (2, 6), (1, 5)]
    (codeMat 161) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_2

end QiushiMatmul
