import QiushiPlane468GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane468GenSource0220 :
    QuotientRankAtLeast (spanCodes [256, 131, 67, 33, 17, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 32), (131, 112), (67, 120), (33, 196), (17, 70), (10, 71), (6, 128)]
    (codeMat 99) (codeMat 473) (codeMat 409) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane468GenSource0221 :
    QuotientRankAtLeast (spanCodes [257, 129, 65, 34, 18, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 327), (129, 326), (65, 325), (34, 440), (18, 432), (10, 424), (7, 256)]
    (codeMat 84) (codeMat 501) (codeMat 494) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane468GenSource0222 :
    QuotientRankAtLeast (spanCodes [259, 128, 64, 33, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 100), (128, 63), (64, 54), (33, 160), (17, 120), (10, 112), (5, 128)]
    (codeMat 95) (codeMat 474) (codeMat 395) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane468GenSource0223 :
    QuotientRankAtLeast (spanCodes [261, 129, 64, 37, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 137), (129, 118), (64, 9), (37, 138), (20, 227), (8, 8), (2, 511)]
    (codeMat 342) (codeMat 183) (codeMat 419) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane468GenSource0224 :
    QuotientRankAtLeast (spanCodes [256, 144, 81, 49, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (144, 3), (81, 484), (49, 416), (8, 256), (5, 8), (2, 24)]
    (codeMat 142) (codeMat 342) (codeMat 215) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane468GenSource0225 :
    QuotientRankAtLeast (spanCodes [288, 161, 64, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(288, 3), (161, 124), (64, 9), (17, 96), (8, 8), (5, 128), (2, 256)]
    (codeMat 86) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane468GenSource0226 :
    QuotientRankAtLeast (spanCodes [260, 128, 65, 36, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 2), (128, 325), (65, 1), (36, 16), (21, 424), (9, 8), (3, 256)]
    (codeMat 93) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane468GenSource0227 :
    QuotientRankAtLeast (spanCodes [261, 129, 65, 37, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 20), (129, 11), (65, 2), (37, 276), (21, 235), (9, 130), (3, 8)]
    (codeMat 397) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane468GenSource0228 :
    QuotientRankAtLeast (spanCodes [288, 161, 65, 16, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(288, 3), (161, 501), (65, 9), (16, 360), (9, 8), (5, 128), (3, 256)]
    (codeMat 94) (codeMat 167) (codeMat 167) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane468GenSource0229 :
    QuotientRankAtLeast (spanCodes [257, 132, 65, 32, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 326), (132, 71), (65, 3), (32, 432), (21, 184), (9, 24), (3, 256)]
    (codeMat 93) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
