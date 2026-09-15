import QiushiGlobalOrbitUnused305Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane305UnusedGenSource0070 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 34, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 232), (130, 360), (66, 104), (34, 235), (22, 373), (10, 105), (1, 8)]
    (codeMat 270) (codeMat 167) (codeMat 167) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane305UnusedGenSource0071 :
    QuotientRankAtLeast (spanCodes [258, 132, 66, 34, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 413), (132, 245), (66, 404), (34, 414), (22, 373), (10, 406), (1, 130)]
    (codeMat 470) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane305UnusedGenSource0072 :
    QuotientRankAtLeast (spanCodes [258, 134, 66, 36, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 483), (134, 252), (66, 28), (36, 360), (22, 245), (10, 29), (1, 3)]
    (codeMat 382) (codeMat 307) (codeMat 311) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane305UnusedGenSource0073 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 38, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 224), (128, 256), (66, 96), (38, 227), (22, 284), (10, 105), (1, 8)]
    (codeMat 271) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane305UnusedGenSource0074 :
    QuotientRankAtLeast (spanCodes [258, 134, 66, 38, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 287), (134, 483), (66, 278), (38, 284), (22, 227), (10, 406), (1, 130)]
    (codeMat 415) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane305UnusedGenSource0075 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 32, 16, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 68), (128, 256), (64, 32), (32, 2), (16, 128), (10, 80), (4, 1), (1, 8)]
    (codeMat 273) (codeMat 140) (codeMat 98) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane305UnusedGenSource0076 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 32, 16, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 69), (130, 325), (64, 32), (32, 2), (16, 130), (10, 81), (4, 1), (1, 8)]
    (codeMat 273) (codeMat 142) (codeMat 354) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane305UnusedGenSource0077 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 34, 16, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 100), (128, 256), (64, 32), (34, 82), (16, 128), (10, 80), (4, 9), (1, 8)]
    (codeMat 273) (codeMat 172) (codeMat 99) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane305UnusedGenSource0078 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 32, 18, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 68), (128, 256), (66, 100), (32, 3), (18, 128), (10, 91), (4, 1), (1, 9)]
    (codeMat 281) (codeMat 141) (codeMat 226) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane305UnusedGenSource0079 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 32, 18, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 69), (130, 325), (66, 101), (32, 3), (18, 130), (10, 90), (4, 1), (1, 9)]
    (codeMat 281) (codeMat 143) (codeMat 482) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
