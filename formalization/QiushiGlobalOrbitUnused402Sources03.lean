import QiushiGlobalOrbitUnused402Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane402UnusedGenSource0030 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 32, 16, 9, 4, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 100), (129, 101), (64, 9), (32, 128), (16, 130), (9, 54), (4, 256), (3, 288)]
    (codeMat 84) (codeMat 395) (codeMat 474) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
