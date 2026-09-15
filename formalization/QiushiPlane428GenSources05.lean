import QiushiPlane428GenData
import QiushiCertifiedTransport
import QiushiOrbit11FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane428GenSource0050 :
    QuotientRankAtLeast (spanCodes [256, 134, 70, 38, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 54), (134, 237), (70, 210), (38, 240), (16, 40), (14, 208), (1, 128)]
    (codeMat 86) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
