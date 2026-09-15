import QiushiGlobalOrbitUnused355Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane355UnusedGenSource0020 :
    QuotientRankAtLeast (spanCodes [260, 132, 64, 32, 20, 12, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 256), (132, 199), (64, 130), (32, 32), (20, 28), (12, 20), (2, 3), (1, 2)]
    (codeMat 337) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
