import QiushiPlane463GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane463GenSource0240 :
    QuotientRankAtLeast (spanCodes [261, 128, 68, 32, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 373), (128, 130), (68, 414), (32, 3), (16, 2), (9, 360), (3, 511)]
    (codeMat 426) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0241 :
    QuotientRankAtLeast (spanCodes [260, 129, 68, 33, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 384), (129, 488), (68, 392), (33, 510), (16, 2), (9, 511), (3, 360)]
    (codeMat 354) (codeMat 377) (codeMat 369) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0242 :
    QuotientRankAtLeast (spanCodes [273, 144, 64, 32, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(273, 407), (144, 511), (64, 8), (32, 130), (9, 1), (4, 128), (3, 384)]
    (codeMat 99) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0243 :
    QuotientRankAtLeast (spanCodes [256, 131, 67, 33, 17, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 3), (131, 20), (67, 22), (33, 235), (17, 276), (10, 406), (7, 8)]
    (codeMat 460) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0244 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 33, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 69), (128, 1), (66, 71), (33, 168), (18, 8), (10, 440), (6, 256)]
    (codeMat 92) (codeMat 335) (codeMat 426) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane463GenSource0245 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 33, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (129, 363), (65, 360), (33, 381), (19, 235), (10, 414), (5, 511)]
    (codeMat 468) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0246 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 32, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (129, 326), (65, 325), (32, 8), (18, 432), (10, 424), (5, 256)]
    (codeMat 84) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane463GenSource0247 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 35, 16, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 258), (128, 1), (65, 256), (35, 373), (16, 8), (10, 97), (5, 130)]
    (codeMat 340) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0248 :
    QuotientRankAtLeast (spanCodes [259, 131, 64, 33, 17, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 393), (131, 265), (64, 256), (33, 227), (17, 97), (10, 105), (4, 511)]
    (codeMat 286) (codeMat 486) (codeMat 157) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0249 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 32, 17, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 104), (130, 360), (64, 384), (32, 9), (17, 29), (10, 30), (4, 8)]
    (codeMat 267) (codeMat 206) (codeMat 498) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
