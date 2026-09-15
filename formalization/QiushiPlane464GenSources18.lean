import QiushiPlane464GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane464GenSource0180 :
    QuotientRankAtLeast (spanCodes [260, 133, 68, 36, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 128), (133, 96), (68, 488), (36, 130), (21, 97), (8, 511), (2, 8)]
    (codeMat 334) (codeMat 107) (codeMat 428) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane464GenSource0181 :
    QuotientRankAtLeast (spanCodes [256, 129, 68, 32, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 130), (129, 245), (68, 278), (32, 128), (21, 96), (8, 384), (2, 360)]
    (codeMat 158) (codeMat 234) (codeMat 461) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane464GenSource0182 :
    QuotientRankAtLeast (spanCodes [261, 132, 68, 36, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 373), (132, 97), (68, 414), (36, 360), (20, 104), (8, 384), (2, 8)]
    (codeMat 143) (codeMat 334) (codeMat 442) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane464GenSource0183 :
    QuotientRankAtLeast (spanCodes [257, 128, 68, 32, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 20), (128, 9), (68, 22), (32, 256), (20, 96), (8, 384), (2, 8)]
    (codeMat 141) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane464GenSource0184 :
    QuotientRankAtLeast (spanCodes [261, 132, 68, 33, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 483), (132, 245), (68, 252), (33, 480), (17, 96), (8, 256), (2, 360)]
    (codeMat 159) (codeMat 230) (codeMat 159) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane464GenSource0185 :
    QuotientRankAtLeast (spanCodes [260, 134, 68, 32, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 1), (134, 70), (68, 324), (32, 8), (18, 432), (10, 416), (1, 256)]
    (codeMat 85) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane464GenSource0186 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 32, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 325), (128, 2), (68, 324), (32, 40), (20, 336), (8, 32), (2, 128), (1, 256)]
    (codeMat 84) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane464GenSource0187 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 36, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (132, 198), (68, 196), (36, 216), (20, 240), (8, 32), (2, 384), (1, 256)]
    (codeMat 84) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane464GenSource0188 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 32, 18, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 452), (130, 455), (64, 2), (32, 32), (18, 504), (10, 464), (4, 256), (1, 128)]
    (codeMat 84) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane464GenSource0189 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 32, 17, 8, 4, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 68), (129, 70), (64, 1), (32, 32), (17, 112), (8, 8), (4, 256), (2, 384)]
    (codeMat 84) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
