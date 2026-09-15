import QiushiGlobalOrbitUnused382Data
import QiushiCertifiedTransport
import QiushiOrbit14FP
import QiushiStep99Orbit68Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane382UnusedGenSource0020 :
    QuotientRankAtLeast (spanCodes [260, 160, 68, 17, 8, 2]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 164, 68, 16, 10, 1] [(260, 448), (160, 164), (68, 224), (17, 10), (8, 16), (2, 27)]
    (codeMat 275) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit68_lb14_unconditional

theorem plane382UnusedGenSource0021 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 32, 19, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (128, 130), (66, 278), (32, 3), (19, 483), (10, 287), (6, 256)]
    (codeMat 102) (codeMat 143) (codeMat 482) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane382UnusedGenSource0022 :
    QuotientRankAtLeast (spanCodes [257, 130, 67, 34, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 20), (130, 130), (67, 278), (34, 284), (19, 483), (10, 287), (7, 256)]
    (codeMat 111) (codeMat 171) (codeMat 485) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
