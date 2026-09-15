import QiushiPlane480GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane480GenSource0220 :
    QuotientRankAtLeast (spanCodes [256, 128, 96, 16, 8, 4, 2, 1]) 6 := by
  apply quotientRankAtLeast_weaken (n := 6) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 64, 16, 8, 4, 2, 1] [(256, 16), (128, 8), (96, 160), (16, 64), (8, 256), (4, 2), (2, 1), (1, 4)]
    (codeMat 161) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_2

end QiushiMatmul
