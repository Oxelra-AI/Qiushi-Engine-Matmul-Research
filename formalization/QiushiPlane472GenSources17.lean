import QiushiPlane472GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane472GenSource0170 :
    QuotientRankAtLeast (spanCodes [261, 133, 68, 37, 16, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 235), (133, 276), (68, 414), (37, 387), (16, 2), (8, 3), (2, 130)]
    (codeMat 234) (codeMat 285) (codeMat 317) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0171 :
    QuotientRankAtLeast (spanCodes [261, 129, 64, 37, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 137), (129, 118), (64, 9), (37, 138), (20, 227), (8, 8), (2, 511)]
    (codeMat 342) (codeMat 183) (codeMat 419) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0172 :
    QuotientRankAtLeast (spanCodes [257, 133, 64, 32, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 126), (133, 413), (64, 9), (32, 511), (20, 284), (9, 8), (3, 130)]
    (codeMat 415) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0173 :
    QuotientRankAtLeast (spanCodes [261, 129, 64, 36, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 136), (129, 104), (64, 8), (36, 3), (20, 508), (9, 1), (3, 360)]
    (codeMat 355) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0174 :
    QuotientRankAtLeast (spanCodes [257, 132, 65, 32, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 326), (132, 71), (65, 3), (32, 432), (21, 184), (9, 24), (3, 256)]
    (codeMat 93) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane472GenSource0175 :
    QuotientRankAtLeast (spanCodes [260, 132, 69, 36, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 1), (132, 324), (69, 70), (36, 8), (17, 160), (8, 432), (2, 256)]
    (codeMat 93) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane472GenSource0176 :
    QuotientRankAtLeast (spanCodes [261, 129, 65, 37, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(261, 71), (129, 324), (65, 1), (37, 440), (21, 416), (8, 8), (2, 256)]
    (codeMat 85) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane472GenSource0177 :
    QuotientRankAtLeast (spanCodes [256, 133, 64, 32, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 2), (133, 68), (64, 3), (32, 16), (20, 160), (8, 24), (2, 256)]
    (codeMat 84) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane472GenSource0178 :
    QuotientRankAtLeast (spanCodes [288, 160, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(288, 325), (160, 69), (68, 168), (16, 1), (8, 2), (2, 8), (1, 16)]
    (codeMat 266) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane472GenSource0179 :
    QuotientRankAtLeast (spanCodes [258, 129, 65, 32, 19, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 136), (129, 232), (65, 384), (32, 130), (19, 235), (10, 414), (6, 8)]
    (codeMat 335) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
