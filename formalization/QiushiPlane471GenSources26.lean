import QiushiPlane471GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane471GenSource0260 :
    QuotientRankAtLeast (spanCodes [257, 145, 81, 32, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 136), (145, 374), (81, 30), (32, 1), (8, 3), (5, 128), (2, 384)]
    (codeMat 106) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane471GenSource0261 :
    QuotientRankAtLeast (spanCodes [256, 144, 81, 33, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 9), (144, 130), (81, 509), (33, 264), (8, 360), (5, 256), (2, 128)]
    (codeMat 95) (codeMat 85) (codeMat 340) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane471GenSource0262 :
    QuotientRankAtLeast (spanCodes [260, 132, 64, 37, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 360), (132, 363), (64, 1), (37, 97), (20, 235), (9, 8), (3, 511)]
    (codeMat 412) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane471GenSource0263 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 37, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 511), (128, 1), (68, 508), (37, 224), (16, 8), (9, 256), (3, 360)]
    (codeMat 212) (codeMat 358) (codeMat 158) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane471GenSource0264 :
    QuotientRankAtLeast (spanCodes [256, 144, 80, 33, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 2), (144, 325), (80, 326), (33, 176), (9, 432), (4, 16), (3, 24)]
    (codeMat 140) (codeMat 234) (codeMat 461) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane471GenSource0265 :
    QuotientRankAtLeast (spanCodes [259, 128, 65, 34, 18, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 182), (128, 219), (65, 63), (34, 240), (18, 216), (10, 248), (7, 128)]
    (codeMat 87) (codeMat 379) (codeMat 247) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane471GenSource0266 :
    QuotientRankAtLeast (spanCodes [259, 130, 67, 34, 16, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 160), (130, 8), (67, 120), (34, 68), (16, 1), (10, 71), (7, 128)]
    (codeMat 106) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane471GenSource0267 :
    QuotientRankAtLeast (spanCodes [258, 131, 67, 35, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 483), (131, 126), (67, 119), (35, 97), (18, 511), (10, 503), (5, 130)]
    (codeMat 470) (codeMat 474) (codeMat 395) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane471GenSource0268 :
    QuotientRankAtLeast (spanCodes [256, 129, 67, 33, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 130), (129, 414), (67, 235), (33, 136), (18, 384), (10, 232), (5, 8)]
    (codeMat 207) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane471GenSource0269 :
    QuotientRankAtLeast (spanCodes [260, 133, 64, 37, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 360), (133, 287), (64, 9), (37, 105), (20, 414), (9, 8), (3, 130)]
    (codeMat 415) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
