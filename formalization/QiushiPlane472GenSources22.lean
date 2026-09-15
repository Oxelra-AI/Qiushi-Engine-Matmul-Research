import QiushiPlane472GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane472GenSource0220 :
    QuotientRankAtLeast (spanCodes [257, 144, 80, 33, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 162), (144, 1), (80, 324), (33, 160), (8, 256), (4, 16), (2, 8)]
    (codeMat 142) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane472GenSource0221 :
    QuotientRankAtLeast (spanCodes [262, 132, 66, 36, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 252), (132, 483), (66, 278), (36, 511), (22, 227), (10, 276), (1, 130)]
    (codeMat 470) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0222 :
    QuotientRankAtLeast (spanCodes [256, 134, 70, 34, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 384), (134, 392), (70, 264), (34, 510), (18, 511), (10, 509), (1, 360)]
    (codeMat 298) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0223 :
    QuotientRankAtLeast (spanCodes [290, 162, 64, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(290, 503), (162, 502), (64, 2), (18, 432), (10, 176), (6, 8), (1, 16)]
    (codeMat 140) (codeMat 444) (codeMat 110) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane472GenSource0224 :
    QuotientRankAtLeast (spanCodes [288, 164, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(288, 325), (164, 237), (68, 168), (16, 3), (8, 2), (2, 24), (1, 16)]
    (codeMat 266) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane472GenSource0225 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 34, 18, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 2), (128, 3), (66, 198), (34, 208), (18, 216), (10, 240), (4, 128), (1, 384)]
    (codeMat 84) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane472GenSource0226 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 34, 16, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (128, 1), (66, 70), (34, 88), (16, 8), (10, 112), (6, 128), (1, 384)]
    (codeMat 84) (codeMat 110) (codeMat 444) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane472GenSource0227 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 32, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 197), (128, 3), (64, 2), (32, 40), (18, 216), (10, 208), (6, 384), (1, 128)]
    (codeMat 84) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane472GenSource0228 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 34, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (130, 455), (64, 2), (34, 472), (18, 504), (10, 464), (6, 256), (1, 128)]
    (codeMat 84) (codeMat 190) (codeMat 355) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane472GenSource0229 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 33, 16, 8, 4, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 70), (129, 68), (64, 1), (33, 112), (16, 32), (8, 8), (4, 384), (2, 256)]
    (codeMat 84) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
