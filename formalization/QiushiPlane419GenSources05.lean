import QiushiPlane419GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiWcOrbit114Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane419GenSource0050 :
    QuotientRankAtLeast (spanCodes [260, 194, 32, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 8, 2, 1] [(260, 1), (194, 258), (32, 8), (10, 416), (1, 256)]
    (codeMat 85) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit114_lb14_wc

theorem plane419GenSource0051 :
    QuotientRankAtLeast (spanCodes [258, 146, 82, 32, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 137), (146, 3), (82, 508), (32, 8), (10, 224), (6, 128), (1, 256)]
    (codeMat 87) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane419GenSource0052 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 32, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (132, 70), (68, 68), (32, 8), (18, 432), (10, 416), (1, 256)]
    (codeMat 84) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane419GenSource0053 :
    QuotientRankAtLeast (spanCodes [260, 130, 68, 32, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 1), (130, 2), (68, 324), (32, 8), (16, 16), (10, 160), (1, 256)]
    (codeMat 85) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane419GenSource0054 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (128, 2), (68, 68), (32, 8), (16, 16), (10, 160), (1, 256)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane419GenSource0055 :
    QuotientRankAtLeast (spanCodes [260, 132, 70, 32, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 3), (132, 326), (70, 68), (32, 24), (18, 432), (10, 416), (1, 256)]
    (codeMat 85) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane419GenSource0056 :
    QuotientRankAtLeast (spanCodes [258, 128, 80, 32, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 393), (128, 511), (80, 284), (32, 8), (10, 480), (6, 384), (1, 256)]
    (codeMat 87) (codeMat 214) (codeMat 214) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane419GenSource0057 :
    QuotientRankAtLeast (spanCodes [256, 128, 70, 32, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 3), (128, 2), (70, 68), (32, 24), (16, 16), (10, 160), (1, 256)]
    (codeMat 84) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane419GenSource0058 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (128, 2), (68, 68), (32, 8), (20, 80), (8, 32), (2, 128), (1, 256)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
