import QiushiPlane315GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane315GenSource0060 :
    QuotientRankAtLeast (spanCodes [258, 128, 80, 32, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 393), (128, 511), (80, 284), (32, 8), (10, 480), (6, 384), (1, 256)]
    (codeMat 87) (codeMat 214) (codeMat 214) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane315GenSource0061 :
    QuotientRankAtLeast (spanCodes [260, 132, 80, 36, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 8), (132, 352), (80, 404), (36, 1), (8, 130), (2, 256), (1, 128)]
    (codeMat 107) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane315GenSource0062 :
    QuotientRankAtLeast (spanCodes [260, 160, 96, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 256), (160, 227), (96, 97), (20, 28), (8, 8), (2, 3), (1, 1)]
    (codeMat 337) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane315GenSource0063 :
    QuotientRankAtLeast (spanCodes [260, 160, 100, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 432), (160, 70), (100, 246), (16, 1), (8, 3), (2, 8), (1, 24)]
    (codeMat 266) (codeMat 299) (codeMat 318) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane315GenSource0064 :
    QuotientRankAtLeast (spanCodes [260, 132, 36, 16, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(260, 360), (132, 104), (36, 5), (16, 9), (8, 18), (2, 8), (1, 16)]
    (codeMat 267) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_7

theorem plane315GenSource0065 :
    QuotientRankAtLeast (spanCodes [260, 128, 66, 32, 18, 10, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(260, 18), (128, 365), (66, 100), (32, 16), (18, 360), (10, 352), (1, 256)]
    (codeMat 87) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_7

theorem plane315GenSource0066 :
    QuotientRankAtLeast (spanCodes [260, 160, 96, 16, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(260, 256), (160, 112), (96, 118), (16, 8), (8, 9), (2, 16), (1, 18)]
    (codeMat 330) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_7

theorem plane315GenSource0067 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 32, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 325), (128, 2), (68, 324), (32, 40), (20, 336), (8, 32), (2, 128), (1, 256)]
    (codeMat 84) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane315GenSource0068 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 32, 16, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 69), (128, 1), (66, 70), (32, 40), (16, 8), (10, 112), (6, 256), (1, 384)]
    (codeMat 84) (codeMat 334) (codeMat 442) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane315GenSource0069 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 32, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 197), (128, 3), (64, 2), (32, 40), (18, 216), (10, 208), (6, 384), (1, 128)]
    (codeMat 84) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
