import QiushiPlane461GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane461GenSource0120 :
    QuotientRankAtLeast (spanCodes [257, 130, 67, 32, 16, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 196), (130, 1), (67, 71), (32, 32), (16, 8), (10, 120), (7, 128)]
    (codeMat 85) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane461GenSource0121 :
    QuotientRankAtLeast (spanCodes [259, 130, 65, 32, 16, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 228), (130, 9), (65, 54), (32, 32), (16, 8), (10, 112), (5, 128)]
    (codeMat 87) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane461GenSource0122 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 33, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 325), (128, 2), (68, 326), (33, 424), (16, 16), (9, 432), (3, 256)]
    (codeMat 84) (codeMat 348) (codeMat 125) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane461GenSource0123 :
    QuotientRankAtLeast (spanCodes [257, 145, 64, 48, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 118), (145, 131), (64, 9), (48, 360), (9, 8), (4, 384), (3, 128)]
    (codeMat 95) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane461GenSource0124 :
    QuotientRankAtLeast (spanCodes [272, 129, 65, 32, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 413), (129, 131), (65, 1), (32, 360), (9, 8), (5, 256), (3, 128)]
    (codeMat 93) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane461GenSource0125 :
    QuotientRankAtLeast (spanCodes [258, 130, 67, 32, 18, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 503), (130, 8), (67, 105), (32, 384), (18, 1), (10, 257), (7, 130)]
    (codeMat 171) (codeMat 355) (codeMat 190) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane461GenSource0126 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 32, 17, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (130, 360), (66, 361), (32, 130), (17, 97), (10, 105), (6, 511)]
    (codeMat 412) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane461GenSource0127 :
    QuotientRankAtLeast (spanCodes [258, 128, 65, 34, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 105), (128, 8), (65, 511), (34, 257), (18, 1), (10, 385), (5, 130)]
    (codeMat 163) (codeMat 335) (codeMat 426) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane461GenSource0128 :
    QuotientRankAtLeast (spanCodes [258, 131, 65, 33, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 414), (131, 227), (65, 511), (33, 392), (17, 224), (10, 480), (5, 8)]
    (codeMat 207) (codeMat 379) (codeMat 247) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane461GenSource0129 :
    QuotientRankAtLeast (spanCodes [259, 128, 64, 34, 18, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 149), (128, 1), (64, 3), (34, 264), (18, 8), (10, 136), (4, 360)]
    (codeMat 156) (codeMat 271) (codeMat 314) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
