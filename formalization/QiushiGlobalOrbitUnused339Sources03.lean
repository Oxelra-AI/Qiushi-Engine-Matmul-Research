import QiushiGlobalOrbitUnused339Data
import QiushiCertifiedTransport
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane339UnusedGenSource0030 :
    QuotientRankAtLeast (spanCodes [256, 134, 70, 36, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (134, 510), (70, 509), (36, 8), (16, 384), (12, 264), (1, 360)]
    (codeMat 156) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
