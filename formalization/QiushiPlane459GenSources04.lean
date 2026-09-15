import QiushiPlane459GenData
import QiushiCertifiedTransport
import QiushiOrbit29FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane459GenSource0040 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 36, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(256, 1), (132, 68), (68, 70), (36, 8), (17, 160), (10, 176)]
    (codeMat 92) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane459GenSource0041 :
    QuotientRankAtLeast (spanCodes [257, 135, 68, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(257, 68), (135, 71), (68, 69), (39, 160), (17, 184), (10, 168)]
    (codeMat 93) (codeMat 467) (codeMat 339) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

end QiushiMatmul
