import QiushiPlane473GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane473GenSource0120 :
    QuotientRankAtLeast (spanCodes [258, 134, 70, 38, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 287), (134, 252), (70, 245), (38, 224), (18, 256), (10, 264), (1, 360)]
    (codeMat 214) (codeMat 485) (codeMat 171) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane473GenSource0121 :
    QuotientRankAtLeast (spanCodes [292, 160, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(292, 511), (160, 71), (68, 184), (16, 1), (8, 2), (2, 8), (1, 16)]
    (codeMat 266) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane473GenSource0122 :
    QuotientRankAtLeast (spanCodes [256, 131, 67, 32, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 3), (131, 70), (67, 71), (32, 24), (18, 432), (10, 440), (5, 256)]
    (codeMat 84) (codeMat 253) (codeMat 415) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane473GenSource0123 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 35, 18, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 68), (128, 1), (66, 71), (35, 160), (18, 8), (10, 440), (4, 256)]
    (codeMat 92) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane473GenSource0124 :
    QuotientRankAtLeast (spanCodes [260, 128, 64, 32, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 1), (128, 256), (64, 128), (32, 8), (20, 97), (10, 276), (1, 130)]
    (codeMat 277) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane473GenSource0125 :
    QuotientRankAtLeast (spanCodes [262, 132, 70, 34, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 235), (132, 414), (70, 227), (34, 363), (18, 360), (10, 362), (1, 511)]
    (codeMat 482) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane473GenSource0126 :
    QuotientRankAtLeast (spanCodes [273, 128, 81, 49, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(273, 229), (128, 3), (81, 228), (49, 416), (8, 256), (5, 8), (2, 24)]
    (codeMat 140) (codeMat 342) (codeMat 215) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane473GenSource0127 :
    QuotientRankAtLeast (spanCodes [261, 128, 65, 32, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(261, 70), (128, 325), (65, 1), (32, 432), (21, 168), (9, 8), (3, 256)]
    (codeMat 93) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane473GenSource0128 :
    QuotientRankAtLeast (spanCodes [273, 129, 81, 49, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(273, 159), (129, 387), (81, 29), (49, 352), (9, 360), (5, 128), (3, 384)]
    (codeMat 85) (codeMat 375) (codeMat 491) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane473GenSource0129 :
    QuotientRankAtLeast (spanCodes [256, 144, 81, 32, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 9), (144, 3), (81, 373), (32, 8), (9, 360), (5, 256), (3, 384)]
    (codeMat 86) (codeMat 87) (codeMat 468) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
