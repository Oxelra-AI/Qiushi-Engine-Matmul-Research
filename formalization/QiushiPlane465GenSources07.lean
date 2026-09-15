import QiushiPlane465GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane465GenSource0070 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 37, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 325), (132, 324), (68, 326), (37, 424), (17, 160), (8, 432), (2, 256)]
    (codeMat 92) (codeMat 460) (codeMat 122) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane465GenSource0071 :
    QuotientRankAtLeast (spanCodes [288, 160, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(288, 325), (160, 69), (68, 168), (16, 1), (8, 2), (2, 8), (1, 16)]
    (codeMat 266) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane465GenSource0072 :
    QuotientRankAtLeast (spanCodes [258, 131, 65, 34, 16, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 414), (131, 227), (65, 511), (34, 30), (16, 3), (10, 31), (5, 8)]
    (codeMat 394) (codeMat 379) (codeMat 247) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane465GenSource0073 :
    QuotientRankAtLeast (spanCodes [259, 130, 64, 35, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 404), (130, 9), (64, 360), (35, 276), (16, 8), (10, 105), (4, 130)]
    (codeMat 407) (codeMat 99) (codeMat 172) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane465GenSource0074 :
    QuotientRankAtLeast (spanCodes [258, 129, 66, 32, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 258), (129, 70), (66, 71), (32, 16), (18, 432), (10, 440), (6, 256)]
    (codeMat 85) (codeMat 249) (codeMat 425) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane465GenSource0075 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 37, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 256), (132, 96), (68, 480), (37, 508), (21, 509), (8, 3), (2, 360)]
    (codeMat 298) (codeMat 395) (codeMat 474) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane465GenSource0076 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 33, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 3), (128, 128), (68, 259), (33, 284), (21, 406), (8, 511), (2, 130)]
    (codeMat 285) (codeMat 125) (codeMat 348) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane465GenSource0077 :
    QuotientRankAtLeast (spanCodes [256, 133, 68, 36, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 130), (133, 483), (68, 278), (36, 128), (20, 136), (9, 384), (3, 360)]
    (codeMat 215) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane465GenSource0078 :
    QuotientRankAtLeast (spanCodes [289, 160, 64, 17, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(289, 502), (160, 414), (64, 8), (17, 131), (9, 1), (4, 384), (3, 128)]
    (codeMat 99) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane465GenSource0079 :
    QuotientRankAtLeast (spanCodes [257, 130, 64, 35, 18, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 68), (130, 3), (64, 325), (35, 160), (18, 24), (10, 424), (4, 256)]
    (codeMat 93) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
