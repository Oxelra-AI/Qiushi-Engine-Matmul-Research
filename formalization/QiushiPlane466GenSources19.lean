import QiushiPlane466GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane466GenSource0190 :
    QuotientRankAtLeast (spanCodes [261, 128, 68, 37, 17, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 373), (128, 130), (68, 235), (37, 29), (17, 10), (9, 3), (3, 8)]
    (codeMat 459) (codeMat 285) (codeMat 317) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane466GenSource0191 :
    QuotientRankAtLeast (spanCodes [256, 133, 68, 32, 17, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 8), (133, 373), (68, 97), (32, 1), (17, 258), (9, 256), (3, 130)]
    (codeMat 226) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane466GenSource0192 :
    QuotientRankAtLeast (spanCodes [257, 132, 68, 32, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 30), (132, 20), (68, 29), (32, 384), (16, 256), (9, 360), (3, 8)]
    (codeMat 141) (codeMat 481) (codeMat 185) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane466GenSource0193 :
    QuotientRankAtLeast (spanCodes [256, 128, 65, 49, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 54), (128, 63), (65, 3), (49, 88), (9, 216), (5, 40), (3, 32)]
    (codeMat 141) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane466GenSource0194 :
    QuotientRankAtLeast (spanCodes [256, 134, 68, 34, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (134, 326), (68, 68), (34, 424), (18, 432), (10, 416), (1, 256)]
    (codeMat 85) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane466GenSource0195 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 50, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 55), (130, 63), (66, 31), (50, 71), (10, 199), (6, 1), (1, 3)]
    (codeMat 161) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane466GenSource0196 :
    QuotientRankAtLeast (spanCodes [288, 164, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(288, 325), (164, 237), (68, 168), (16, 3), (8, 2), (2, 24), (1, 16)]
    (codeMat 266) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane466GenSource0197 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 32, 18, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 452), (130, 455), (64, 2), (32, 32), (18, 504), (10, 464), (4, 256), (1, 128)]
    (codeMat 84) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane466GenSource0198 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 33, 16, 8, 4, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 2), (129, 68), (64, 1), (33, 80), (16, 32), (8, 8), (4, 128), (2, 256)]
    (codeMat 84) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane466GenSource0199 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 33, 17, 8, 4, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 70), (128, 2), (64, 1), (33, 112), (17, 80), (8, 8), (4, 384), (2, 128)]
    (codeMat 84) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
