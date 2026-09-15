import QiushiPlane455GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane455GenSource0100 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 34, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 352), (129, 480), (64, 256), (34, 21), (17, 31), (10, 28), (5, 8)]
    (codeMat 267) (codeMat 470) (codeMat 213) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane455GenSource0101 :
    QuotientRankAtLeast (spanCodes [257, 129, 65, 35, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 258), (129, 257), (65, 256), (35, 503), (17, 105), (10, 97), (5, 130)]
    (codeMat 348) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane455GenSource0102 :
    QuotientRankAtLeast (spanCodes [289, 129, 64, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(289, 60), (129, 138), (64, 219), (16, 128), (9, 216), (4, 32), (3, 8)]
    (codeMat 143) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane455GenSource0103 :
    QuotientRankAtLeast (spanCodes [320, 129, 33, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(320, 128), (129, 240), (33, 52), (16, 3), (9, 54), (4, 32), (3, 40)]
    (codeMat 266) (codeMat 346) (codeMat 459) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane455GenSource0104 :
    QuotientRankAtLeast (spanCodes [256, 129, 66, 35, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 360), (129, 126), (66, 119), (35, 105), (18, 511), (10, 503), (6, 130)]
    (codeMat 407) (codeMat 478) (codeMat 445) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane455GenSource0105 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 32, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 2), (129, 326), (65, 325), (32, 16), (18, 432), (10, 424), (6, 256)]
    (codeMat 84) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane455GenSource0106 :
    QuotientRankAtLeast (spanCodes [258, 129, 67, 35, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 245), (129, 287), (67, 483), (35, 503), (17, 284), (10, 227), (5, 130)]
    (codeMat 470) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane455GenSource0107 :
    QuotientRankAtLeast (spanCodes [256, 129, 66, 33, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 9), (129, 31), (66, 28), (33, 105), (16, 511), (10, 284), (4, 8)]
    (codeMat 397) (codeMat 214) (codeMat 214) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane455GenSource0108 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 36, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 3), (129, 69), (64, 1), (36, 24), (20, 424), (9, 8), (3, 256)]
    (codeMat 92) (codeMat 167) (codeMat 167) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane455GenSource0109 :
    QuotientRankAtLeast (spanCodes [256, 129, 69, 33, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 511), (129, 363), (69, 510), (33, 392), (20, 480), (9, 384), (3, 360)]
    (codeMat 213) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
