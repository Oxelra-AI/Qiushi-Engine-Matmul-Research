import QiushiPlane463GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane463GenSource0210 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (128, 1), (68, 20), (32, 128), (17, 96), (8, 256), (2, 8)]
    (codeMat 140) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0211 :
    QuotientRankAtLeast (spanCodes [261, 133, 68, 37, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 235), (133, 227), (68, 414), (37, 363), (17, 149), (8, 360), (2, 511)]
    (codeMat 419) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0212 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 36, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 8), (132, 264), (68, 392), (36, 1), (17, 149), (8, 511), (2, 360)]
    (codeMat 299) (codeMat 207) (codeMat 370) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0213 :
    QuotientRankAtLeast (spanCodes [257, 129, 68, 37, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 119), (129, 245), (68, 126), (37, 392), (21, 264), (8, 384), (2, 360)]
    (codeMat 158) (codeMat 494) (codeMat 501) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0214 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 38, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 325), (132, 326), (68, 324), (38, 424), (16, 432), (10, 160), (1, 256)]
    (codeMat 92) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane463GenSource0215 :
    QuotientRankAtLeast (spanCodes [276, 148, 68, 36, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(276, 483), (148, 28), (68, 150), (36, 256), (8, 130), (2, 3), (1, 2)]
    (codeMat 241) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0216 :
    QuotientRankAtLeast (spanCodes [288, 160, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(288, 325), (160, 69), (68, 168), (16, 1), (8, 2), (2, 8), (1, 16)]
    (codeMat 266) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane463GenSource0217 :
    QuotientRankAtLeast (spanCodes [259, 128, 64, 35, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 96), (128, 128), (64, 384), (35, 97), (16, 130), (10, 406), (4, 8)]
    (codeMat 270) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0218 :
    QuotientRankAtLeast (spanCodes [257, 130, 64, 35, 18, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 68), (130, 3), (64, 325), (35, 160), (18, 24), (10, 424), (4, 256)]
    (codeMat 93) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane463GenSource0219 :
    QuotientRankAtLeast (spanCodes [257, 128, 66, 33, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 276), (128, 8), (66, 105), (33, 148), (18, 1), (10, 361), (6, 511)]
    (codeMat 419) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
