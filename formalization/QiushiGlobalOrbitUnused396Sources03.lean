import QiushiGlobalOrbitUnused396Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane396UnusedGenSource0030 :
    QuotientRankAtLeast (spanCodes [257, 131, 66, 34, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 246), (131, 235), (66, 373), (34, 10), (18, 8), (10, 138), (6, 3)]
    (codeMat 467) (codeMat 125) (codeMat 348) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane396UnusedGenSource0031 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 33, 17, 8, 5, 2]) 6 := by
  apply quotientRankAtLeast_weaken (n := 6) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 64, 16, 8, 4, 2, 1] [(257, 91), (128, 24), (65, 64), (33, 420), (17, 160), (8, 256), (5, 18), (2, 16)]
    (codeMat 141) (codeMat 372) (codeMat 93) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_2

end QiushiMatmul
