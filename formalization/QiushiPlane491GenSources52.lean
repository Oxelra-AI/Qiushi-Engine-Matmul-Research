import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiOrbit25FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0520 :
    QuotientRankAtLeast (spanCodes [257, 136, 72, 40, 25, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 385), (136, 381), (72, 511), (40, 8), (25, 23), (5, 1), (3, 2)]
    (codeMat 337) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0521 :
    QuotientRankAtLeast (spanCodes [264, 137, 65, 42, 18, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(264, 343), (137, 81), (65, 260), (42, 15), (18, 8), (7, 6)]
    (codeMat 355) (codeMat 369) (codeMat 377) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane491GenSource0522 :
    QuotientRankAtLeast (spanCodes [256, 128, 64, 35, 16, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(256, 1), (128, 4), (64, 6), (35, 80), (16, 256), (4, 8)]
    (codeMat 140) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane491GenSource0523 :
    QuotientRankAtLeast (spanCodes [257, 136, 73, 40, 24, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 440), (136, 327), (73, 511), (40, 1), (24, 2), (5, 8), (3, 16)]
    (codeMat 266) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0524 :
    QuotientRankAtLeast (spanCodes [256, 137, 73, 41, 25, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (137, 509), (73, 511), (41, 440), (25, 184), (4, 8), (3, 16)]
    (codeMat 140) (codeMat 207) (codeMat 370) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0525 :
    QuotientRankAtLeast (spanCodes [265, 128, 73, 33, 24, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(265, 510), (128, 3), (73, 511), (33, 440), (24, 256), (5, 8), (2, 24)]
    (codeMat 140) (codeMat 379) (codeMat 247) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0526 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 33, 17, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 30), (128, 8), (65, 54), (33, 198), (17, 70), (4, 3), (2, 1)]
    (codeMat 161) (codeMat 110) (codeMat 444) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane491GenSource0527 :
    QuotientRankAtLeast (spanCodes [257, 137, 72, 40, 24, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 224), (137, 119), (72, 511), (40, 3), (24, 1), (4, 256), (2, 384)]
    (codeMat 106) (codeMat 473) (codeMat 409) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0528 :
    QuotientRankAtLeast (spanCodes [266, 138, 64, 40, 18, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(266, 247), (138, 246), (64, 3), (40, 256), (18, 432), (6, 8), (1, 24)]
    (codeMat 140) (codeMat 445) (codeMat 478) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0529 :
    QuotientRankAtLeast (spanCodes [260, 140, 72, 44, 28, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 511), (140, 187), (72, 1), (44, 440), (28, 184), (2, 24), (1, 8)]
    (codeMat 142) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
