import QiushiGlobalOrbitUnused394Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane394UnusedGenSource0030 :
    QuotientRankAtLeast (spanCodes [256, 64, 33, 16, 8, 4, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 32, 20, 8, 2, 1] [(256, 256), (64, 128), (33, 20), (16, 1), (8, 2), (4, 32), (2, 8)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_12

theorem plane394UnusedGenSource0031 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 33, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (130, 128), (64, 8), (33, 28), (16, 256), (10, 224), (4, 3)]
    (codeMat 172) (codeMat 140) (codeMat 98) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
