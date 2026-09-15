import QiushiPlane476GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane476GenSource0100 :
    QuotientRankAtLeast (spanCodes [272, 144, 65, 33, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 508), (144, 3), (65, 9), (33, 352), (9, 8), (4, 256), (3, 128)]
    (codeMat 94) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane476GenSource0101 :
    QuotientRankAtLeast (spanCodes [273, 129, 81, 49, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(273, 159), (129, 387), (81, 29), (49, 352), (9, 360), (5, 128), (3, 384)]
    (codeMat 85) (codeMat 375) (codeMat 491) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane476GenSource0102 :
    QuotientRankAtLeast (spanCodes [259, 130, 66, 34, 16, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 264), (130, 128), (66, 488), (34, 20), (16, 2), (10, 23), (7, 8)]
    (codeMat 330) (codeMat 345) (codeMat 345) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane476GenSource0103 :
    QuotientRankAtLeast (spanCodes [259, 128, 64, 32, 16, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 352), (128, 128), (64, 384), (32, 1), (16, 2), (10, 150), (7, 360)]
    (codeMat 298) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane476GenSource0104 :
    QuotientRankAtLeast (spanCodes [258, 130, 67, 35, 18, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 324), (130, 1), (67, 71), (35, 160), (18, 8), (10, 440), (4, 256)]
    (codeMat 93) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane476GenSource0105 :
    QuotientRankAtLeast (spanCodes [256, 133, 69, 37, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 3), (133, 257), (69, 259), (37, 284), (20, 235), (9, 511), (3, 130)]
    (codeMat 340) (codeMat 239) (codeMat 351) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane476GenSource0106 :
    QuotientRankAtLeast (spanCodes [272, 145, 65, 33, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 252), (145, 127), (65, 1), (33, 352), (9, 8), (4, 256), (3, 384)]
    (codeMat 93) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane476GenSource0107 :
    QuotientRankAtLeast (spanCodes [256, 160, 96, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (160, 68), (96, 70), (16, 256), (9, 432), (4, 8), (3, 16)]
    (codeMat 140) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane476GenSource0108 :
    QuotientRankAtLeast (spanCodes [272, 145, 64, 32, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 22), (145, 118), (64, 8), (32, 2), (8, 1), (4, 128), (2, 384)]
    (codeMat 98) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane476GenSource0109 :
    QuotientRankAtLeast (spanCodes [276, 132, 80, 48, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(276, 508), (132, 480), (80, 20), (48, 3), (8, 2), (2, 256), (1, 128)]
    (codeMat 98) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
