import QiushiGlobalOrbitUnused203Data
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit8Closed
import QiushiPlane152GenBindings00
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane203UnusedGenSource0010 :
    QuotientRankAtLeast (spanCodes [272, 134, 68, 54, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(272, 175), (134, 353), (68, 96), (54, 27), (10, 196), (1, 256)]
    (codeMat 117) (codeMat 482) (codeMat 143) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane152GenBound0001

theorem plane203UnusedGenSource0011 :
    QuotientRankAtLeast (spanCodes [272, 176, 64, 8, 4, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 64, 8, 4, 2, 1] [(272, 304), (176, 160), (64, 72), (8, 8), (4, 4), (2, 2), (1, 1)]
    (codeMat 401) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit8_lb9

theorem plane203UnusedGenSource0012 :
    QuotientRankAtLeast (spanCodes [256, 160, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 256), (160, 160), (68, 68), (16, 16), (8, 8), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane203UnusedGenSource0013 :
    QuotientRankAtLeast (spanCodes [256, 160, 64, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 16), (160, 160), (64, 2), (16, 256), (10, 68), (4, 8), (1, 1)]
    (codeMat 161) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane203UnusedGenSource0014 :
    QuotientRankAtLeast (spanCodes [256, 160, 66, 16, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 432), (160, 160), (66, 70), (16, 256), (10, 68), (6, 8), (1, 1)]
    (codeMat 177) (codeMat 417) (codeMat 177) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
