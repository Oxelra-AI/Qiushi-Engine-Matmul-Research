import QiushiPlane456GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane456GenSource0220 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 33, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 69), (128, 1), (66, 71), (33, 168), (18, 8), (10, 440), (6, 256)]
    (codeMat 92) (codeMat 335) (codeMat 426) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane456GenSource0221 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 33, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 327), (128, 3), (65, 325), (33, 184), (18, 24), (10, 424), (6, 256)]
    (codeMat 92) (codeMat 375) (codeMat 491) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane456GenSource0222 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 32, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 2), (129, 326), (65, 325), (32, 16), (18, 432), (10, 424), (6, 256)]
    (codeMat 84) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane456GenSource0223 :
    QuotientRankAtLeast (spanCodes [321, 128, 33, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(321, 248), (128, 128), (33, 60), (16, 2), (9, 63), (4, 32), (3, 40)]
    (codeMat 266) (codeMat 345) (codeMat 345) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane456GenSource0224 :
    QuotientRankAtLeast (spanCodes [256, 129, 69, 32, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 130), (129, 284), (69, 138), (32, 2), (20, 149), (8, 3), (2, 511)]
    (codeMat 426) (codeMat 187) (codeMat 229) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane456GenSource0225 :
    QuotientRankAtLeast (spanCodes [321, 128, 33, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(321, 197), (128, 128), (33, 53), (17, 21), (8, 40), (5, 3), (2, 2)]
    (codeMat 273) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane456GenSource0226 :
    QuotientRankAtLeast (spanCodes [288, 160, 64, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(288, 325), (160, 326), (64, 2), (18, 432), (10, 176), (6, 24), (1, 16)]
    (codeMat 140) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane456GenSource0227 :
    QuotientRankAtLeast (spanCodes [288, 160, 66, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(288, 1), (160, 324), (66, 162), (16, 256), (10, 160), (4, 8), (1, 16)]
    (codeMat 142) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane456GenSource0228 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 32, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 325), (128, 2), (68, 324), (32, 40), (20, 336), (8, 32), (2, 128), (1, 256)]
    (codeMat 84) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane456GenSource0229 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 36, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (132, 198), (68, 196), (36, 216), (20, 240), (8, 32), (2, 384), (1, 256)]
    (codeMat 84) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
