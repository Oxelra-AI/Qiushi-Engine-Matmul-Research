import QiushiPlane474GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane474GenSource0110 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 33, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 325), (128, 2), (68, 326), (33, 424), (16, 16), (9, 432), (3, 256)]
    (codeMat 84) (codeMat 348) (codeMat 125) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane474GenSource0111 :
    QuotientRankAtLeast (spanCodes [260, 132, 65, 32, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 1), (132, 324), (65, 3), (32, 8), (21, 160), (8, 24), (2, 256)]
    (codeMat 85) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane474GenSource0112 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 36, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (129, 149), (64, 2), (36, 8), (20, 264), (8, 128), (2, 360)]
    (codeMat 156) (codeMat 142) (codeMat 354) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane474GenSource0113 :
    QuotientRankAtLeast (spanCodes [258, 132, 70, 36, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 150), (132, 148), (70, 509), (36, 384), (18, 256), (10, 264), (1, 360)]
    (codeMat 213) (codeMat 481) (codeMat 185) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane474GenSource0114 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 36, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 385), (130, 384), (64, 2), (36, 511), (20, 503), (10, 406), (1, 130)]
    (codeMat 340) (codeMat 444) (codeMat 110) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane474GenSource0115 :
    QuotientRankAtLeast (spanCodes [258, 128, 65, 33, 16, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 126), (128, 9), (65, 360), (33, 381), (16, 8), (10, 105), (5, 130)]
    (codeMat 470) (codeMat 359) (codeMat 174) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane474GenSource0116 :
    QuotientRankAtLeast (spanCodes [259, 131, 64, 34, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 386), (131, 387), (64, 3), (34, 97), (19, 235), (10, 414), (7, 130)]
    (codeMat 348) (codeMat 395) (codeMat 474) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane474GenSource0117 :
    QuotientRankAtLeast (spanCodes [258, 128, 67, 34, 17, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 257), (128, 325), (67, 327), (34, 264), (17, 168), (10, 184), (6, 256)]
    (codeMat 93) (codeMat 207) (codeMat 370) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane474GenSource0118 :
    QuotientRankAtLeast (spanCodes [259, 130, 64, 35, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 224), (130, 128), (64, 360), (35, 227), (18, 130), (10, 381), (6, 8)]
    (codeMat 334) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane474GenSource0119 :
    QuotientRankAtLeast (spanCodes [258, 132, 64, 36, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 23), (132, 21), (64, 9), (36, 511), (20, 381), (10, 105), (1, 8)]
    (codeMat 461) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
