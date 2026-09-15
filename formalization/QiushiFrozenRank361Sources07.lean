import QiushiFrozenRank361Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane361RankCoverGenSource0070 :
    QuotientRankAtLeast (spanCodes [262, 128, 66, 38, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 232), (128, 360), (66, 96), (38, 235), (20, 373), (10, 97), (1, 8)]
    (codeMat 334) (codeMat 167) (codeMat 167) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane361RankCoverGenSource0071 :
    QuotientRankAtLeast (spanCodes [262, 134, 66, 38, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 413), (134, 245), (66, 278), (38, 414), (20, 373), (10, 276), (1, 130)]
    (codeMat 478) (codeMat 188) (codeMat 103) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane361RankCoverGenSource0072 :
    QuotientRankAtLeast (spanCodes [262, 130, 68, 32, 20, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 284), (130, 511), (68, 224), (32, 8), (20, 105), (12, 96), (1, 256)]
    (codeMat 114) (codeMat 242) (codeMat 205) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane361RankCoverGenSource0073 :
    QuotientRankAtLeast (spanCodes [262, 134, 68, 32, 20, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 284), (134, 227), (68, 480), (32, 8), (20, 97), (12, 96), (1, 256)]
    (codeMat 122) (codeMat 226) (codeMat 141) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane361RankCoverGenSource0074 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 36, 20, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 29), (128, 3), (64, 1), (36, 360), (20, 232), (12, 104), (1, 8)]
    (codeMat 140) (codeMat 279) (codeMat 279) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane361RankCoverGenSource0075 :
    QuotientRankAtLeast (spanCodes [258, 132, 64, 36, 20, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 21), (132, 23), (64, 9), (36, 360), (20, 488), (12, 104), (1, 8)]
    (codeMat 141) (codeMat 407) (codeMat 405) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane361RankCoverGenSource0076 :
    QuotientRankAtLeast (spanCodes [260, 134, 68, 32, 20, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 2), (134, 21), (68, 509), (32, 3), (20, 29), (14, 245), (1, 360)]
    (codeMat 431) (codeMat 92) (codeMat 116) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane361RankCoverGenSource0077 :
    QuotientRankAtLeast (spanCodes [262, 130, 70, 34, 20, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 227), (130, 511), (70, 224), (34, 97), (20, 105), (14, 352), (1, 256)]
    (codeMat 123) (codeMat 470) (codeMat 213) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane361RankCoverGenSource0078 :
    QuotientRankAtLeast (spanCodes [262, 134, 70, 34, 20, 14, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(262, 118), (134, 127), (70, 100), (34, 112), (20, 120), (14, 352), (1, 256)]
    (codeMat 95) (codeMat 498) (codeMat 206) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_7

theorem plane361RankCoverGenSource0079 :
    QuotientRankAtLeast (spanCodes [256, 128, 64, 36, 20, 14, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(256, 2), (128, 7), (64, 4), (36, 16), (20, 376), (14, 96), (1, 256)]
    (codeMat 92) (codeMat 242) (codeMat 205) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_7

end QiushiMatmul
