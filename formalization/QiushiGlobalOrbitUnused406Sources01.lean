import QiushiGlobalOrbitUnused406Data
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiWcOrbit202Dispatch
import QiushiWcOrbit213Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane406UnusedGenSource0010 :
    QuotientRankAtLeast (spanCodes [276, 130, 68, 49, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(276, 10), (130, 1), (68, 506), (49, 373), (10, 97)]
    (codeMat 405) (codeMat 99) (codeMat 172) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane406UnusedGenSource0011 :
    QuotientRankAtLeast (spanCodes [276, 128, 68, 51, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(276, 496), (128, 1), (68, 506), (51, 276), (10, 97)]
    (codeMat 468) (codeMat 359) (codeMat 174) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane406UnusedGenSource0012 :
    QuotientRankAtLeast (spanCodes [276, 134, 68, 53, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(276, 287), (134, 238), (68, 411), (53, 96), (10, 97)]
    (codeMat 179) (codeMat 239) (codeMat 351) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane406UnusedGenSource0013 :
    QuotientRankAtLeast (spanCodes [276, 133, 68, 54, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(276, 132), (133, 238), (68, 411), (54, 1), (10, 97)]
    (codeMat 187) (codeMat 459) (codeMat 346) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane406UnusedGenSource0014 :
    QuotientRankAtLeast (spanCodes [272, 178, 64, 10, 4, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 68, 8, 2, 1] [(272, 312), (178, 400), (64, 3), (10, 76), (4, 8), (1, 1)]
    (codeMat 169) (codeMat 177) (codeMat 417) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109wc202s9Dispatch

theorem plane406UnusedGenSource0015 :
    QuotientRankAtLeast (spanCodes [260, 160, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 256), (160, 162), (68, 69), (16, 16), (8, 8), (2, 2), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane406UnusedGenSource0016 :
    QuotientRankAtLeast (spanCodes [257, 129, 66, 33, 19, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 20), (129, 404), (66, 278), (33, 28), (19, 252), (10, 287), (6, 256)]
    (codeMat 110) (codeMat 185) (codeMat 481) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane406UnusedGenSource0017 :
    QuotientRankAtLeast (spanCodes [256, 131, 67, 35, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (131, 404), (67, 278), (35, 259), (19, 252), (10, 287), (7, 256)]
    (codeMat 103) (codeMat 157) (codeMat 486) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
