import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiOrbit25FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0560 :
    QuotientRankAtLeast (spanCodes [266, 137, 72, 42, 25, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(266, 94), (137, 338), (72, 7), (42, 88), (25, 336), (5, 8)]
    (codeMat 206) (codeMat 377) (codeMat 369) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane491GenSource0561 :
    QuotientRankAtLeast (spanCodes [257, 129, 66, 34, 19, 9, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 392), (129, 224), (66, 480), (34, 414), (19, 227), (9, 511), (5, 8)]
    (codeMat 335) (codeMat 379) (codeMat 247) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0562 :
    QuotientRankAtLeast (spanCodes [257, 130, 66, 33, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 136), (130, 384), (66, 232), (33, 138), (19, 414), (10, 235), (5, 8)]
    (codeMat 334) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0563 :
    QuotientRankAtLeast (spanCodes [256, 131, 64, 32, 18, 8, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 2), (131, 326), (64, 3), (32, 16), (18, 432), (8, 24), (6, 256)]
    (codeMat 84) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0564 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 35, 18, 9, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 69), (128, 1), (64, 2), (35, 424), (18, 8), (9, 16), (6, 256)]
    (codeMat 92) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0565 :
    QuotientRankAtLeast (spanCodes [258, 129, 65, 34, 19, 9, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 259), (129, 327), (65, 2), (34, 280), (19, 184), (9, 16), (6, 256)]
    (codeMat 93) (codeMat 190) (codeMat 355) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0566 :
    QuotientRankAtLeast (spanCodes [258, 131, 64, 32, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 258), (131, 326), (64, 325), (32, 16), (18, 432), (10, 424), (6, 256)]
    (codeMat 85) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0567 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 35, 16, 11, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 69), (128, 1), (66, 71), (35, 424), (16, 8), (11, 440), (6, 256)]
    (codeMat 84) (codeMat 335) (codeMat 426) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0568 :
    QuotientRankAtLeast (spanCodes [257, 128, 67, 35, 16, 9, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 100), (128, 219), (67, 237), (35, 160), (16, 216), (9, 40), (7, 128)]
    (codeMat 94) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane491GenSource0569 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 33, 17, 9, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 327), (130, 325), (66, 326), (33, 440), (17, 424), (9, 432), (7, 256)]
    (codeMat 84) (codeMat 494) (codeMat 501) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
