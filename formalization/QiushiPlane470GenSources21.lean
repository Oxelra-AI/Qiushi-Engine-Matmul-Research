import QiushiPlane470GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane470GenSource0210 :
    QuotientRankAtLeast (spanCodes [257, 144, 80, 33, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 162), (144, 1), (80, 324), (33, 160), (8, 256), (4, 16), (2, 8)]
    (codeMat 142) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane470GenSource0211 :
    QuotientRankAtLeast (spanCodes [257, 160, 65, 17, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 502), (160, 276), (65, 9), (17, 96), (8, 8), (4, 384), (2, 256)]
    (codeMat 87) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane470GenSource0212 :
    QuotientRankAtLeast (spanCodes [258, 130, 70, 38, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 327), (130, 2), (70, 68), (38, 184), (18, 16), (10, 416), (1, 256)]
    (codeMat 93) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane470GenSource0213 :
    QuotientRankAtLeast (spanCodes [258, 132, 70, 32, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 480), (132, 224), (70, 264), (32, 3), (18, 511), (10, 509), (1, 360)]
    (codeMat 354) (codeMat 247) (codeMat 379) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane470GenSource0214 :
    QuotientRankAtLeast (spanCodes [256, 164, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 256), (164, 228), (68, 160), (16, 3), (8, 2), (2, 24), (1, 16)]
    (codeMat 266) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane470GenSource0215 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 32, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 197), (128, 3), (64, 2), (32, 40), (18, 216), (10, 208), (6, 384), (1, 128)]
    (codeMat 84) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane470GenSource0216 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 33, 16, 8, 4, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 70), (129, 68), (64, 1), (33, 112), (16, 32), (8, 8), (4, 384), (2, 256)]
    (codeMat 84) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane470GenSource0217 :
    QuotientRankAtLeast (spanCodes [257, 129, 65, 32, 17, 8, 4, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 324), (129, 326), (65, 325), (32, 32), (17, 368), (8, 40), (4, 256), (2, 384)]
    (codeMat 84) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane470GenSource0218 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 33, 17, 8, 4, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 326), (128, 2), (65, 325), (33, 368), (17, 336), (8, 40), (4, 384), (2, 128)]
    (codeMat 84) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane470GenSource0219 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 32, 17, 9, 5, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (129, 199), (64, 3), (32, 8), (17, 248), (9, 216), (5, 128), (3, 256)]
    (codeMat 84) (codeMat 159) (codeMat 230) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
