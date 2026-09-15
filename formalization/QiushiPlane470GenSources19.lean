import QiushiPlane470GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane470GenSource0190 :
    QuotientRankAtLeast (spanCodes [258, 128, 80, 48, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 118), (128, 511), (80, 284), (48, 8), (10, 480), (4, 384), (1, 256)]
    (codeMat 87) (codeMat 498) (codeMat 206) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane470GenSource0191 :
    QuotientRankAtLeast (spanCodes [258, 128, 82, 50, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 509), (128, 360), (82, 245), (50, 21), (10, 29), (6, 2), (1, 3)]
    (codeMat 401) (codeMat 431) (codeMat 477) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane470GenSource0192 :
    QuotientRankAtLeast (spanCodes [259, 128, 67, 33, 17, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 240), (128, 32), (67, 248), (33, 70), (17, 196), (10, 199), (6, 128)]
    (codeMat 99) (codeMat 489) (codeMat 241) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane470GenSource0193 :
    QuotientRankAtLeast (spanCodes [259, 128, 65, 35, 16, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 374), (128, 9), (65, 256), (35, 373), (16, 8), (10, 105), (5, 511)]
    (codeMat 342) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane470GenSource0194 :
    QuotientRankAtLeast (spanCodes [257, 133, 65, 36, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 488), (133, 96), (65, 128), (36, 511), (21, 105), (8, 130), (2, 8)]
    (codeMat 335) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane470GenSource0195 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 33, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 257), (128, 128), (65, 1), (33, 105), (21, 276), (8, 8), (2, 130)]
    (codeMat 277) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane470GenSource0196 :
    QuotientRankAtLeast (spanCodes [257, 128, 81, 49, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 387), (128, 130), (81, 149), (49, 264), (8, 360), (5, 384), (2, 128)]
    (codeMat 93) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane470GenSource0197 :
    QuotientRankAtLeast (spanCodes [257, 160, 64, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 127), (160, 28), (64, 9), (17, 96), (8, 8), (5, 384), (2, 256)]
    (codeMat 86) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane470GenSource0198 :
    QuotientRankAtLeast (spanCodes [256, 144, 80, 33, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 2), (144, 325), (80, 326), (33, 176), (9, 432), (4, 16), (3, 24)]
    (codeMat 140) (codeMat 234) (codeMat 461) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane470GenSource0199 :
    QuotientRankAtLeast (spanCodes [259, 128, 65, 34, 18, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 182), (128, 219), (65, 63), (34, 240), (18, 216), (10, 248), (7, 128)]
    (codeMat 87) (codeMat 379) (codeMat 247) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
