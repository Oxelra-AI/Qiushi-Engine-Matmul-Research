import QiushiPlane466GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane466GenSource0170 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 35, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 256), (129, 488), (65, 360), (35, 276), (18, 511), (10, 381), (5, 8)]
    (codeMat 270) (codeMat 467) (codeMat 339) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane466GenSource0171 :
    QuotientRankAtLeast (spanCodes [257, 130, 67, 34, 18, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 70), (130, 3), (67, 199), (34, 240), (18, 216), (10, 248), (7, 128)]
    (codeMat 85) (codeMat 379) (codeMat 247) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane466GenSource0172 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 33, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 69), (128, 1), (66, 71), (33, 168), (18, 8), (10, 440), (6, 256)]
    (codeMat 92) (codeMat 335) (codeMat 426) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane466GenSource0173 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 50, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 60), (130, 63), (64, 1), (50, 248), (10, 120), (4, 32), (1, 8)]
    (codeMat 140) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane466GenSource0174 :
    QuotientRankAtLeast (spanCodes [259, 131, 67, 34, 16, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 352), (131, 224), (67, 480), (34, 29), (16, 3), (10, 31), (7, 8)]
    (codeMat 266) (codeMat 351) (codeMat 239) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane466GenSource0175 :
    QuotientRankAtLeast (spanCodes [259, 129, 65, 32, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 406), (129, 381), (65, 511), (32, 384), (18, 360), (10, 488), (5, 8)]
    (codeMat 142) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane466GenSource0176 :
    QuotientRankAtLeast (spanCodes [258, 128, 65, 33, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 406), (128, 130), (65, 511), (33, 392), (18, 128), (10, 488), (5, 8)]
    (codeMat 207) (codeMat 377) (codeMat 369) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane466GenSource0177 :
    QuotientRankAtLeast (spanCodes [257, 131, 65, 32, 16, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 10), (131, 28), (65, 3), (32, 128), (16, 256), (10, 224), (5, 8)]
    (codeMat 141) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane466GenSource0178 :
    QuotientRankAtLeast (spanCodes [256, 130, 65, 33, 16, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 9), (130, 128), (65, 384), (33, 503), (16, 130), (10, 276), (5, 511)]
    (codeMat 351) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane466GenSource0179 :
    QuotientRankAtLeast (spanCodes [256, 133, 68, 36, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 9), (133, 404), (68, 126), (36, 8), (21, 276), (8, 511), (2, 130)]
    (codeMat 415) (codeMat 93) (codeMat 372) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
