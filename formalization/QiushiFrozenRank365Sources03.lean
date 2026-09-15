import QiushiFrozenRank365Data
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane365RankCoverGenSource0030 :
    QuotientRankAtLeast (spanCodes [264, 128, 76, 32, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(264, 413), (128, 3), (76, 278), (32, 360), (20, 149), (2, 2), (1, 130)]
    (codeMat 461) (codeMat 355) (codeMat 190) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane365RankCoverGenSource0031 :
    QuotientRankAtLeast (spanCodes [264, 132, 64, 36, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(264, 224), (132, 148), (64, 256), (36, 360), (20, 151), (2, 2), (1, 128)]
    (codeMat 271) (codeMat 354) (codeMat 142) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane365RankCoverGenSource0032 :
    QuotientRankAtLeast (spanCodes [264, 132, 72, 36, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(264, 418), (132, 76), (72, 18), (36, 256), (20, 69), (2, 1), (1, 2)]
    (codeMat 249) (codeMat 266) (codeMat 266) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit10_lb12

theorem plane365RankCoverGenSource0033 :
    QuotientRankAtLeast (spanCodes [256, 160, 64, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (160, 68), (64, 2), (16, 256), (10, 160), (4, 8), (1, 16)]
    (codeMat 140) (codeMat 140) (codeMat 98) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit10_lb12

theorem plane365RankCoverGenSource0034 :
    QuotientRankAtLeast (spanCodes [256, 160, 96, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (160, 149), (96, 21), (16, 360), (10, 96), (4, 1), (1, 8)]
    (codeMat 225) (codeMat 156) (codeMat 102) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane365RankCoverGenSource0035 :
    QuotientRankAtLeast (spanCodes [266, 138, 72, 42, 16, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(266, 84), (138, 484), (72, 18), (42, 68), (16, 256), (4, 8), (1, 9)]
    (codeMat 177) (codeMat 169) (codeMat 225) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit10_lb12

theorem plane365RankCoverGenSource0036 :
    QuotientRankAtLeast (spanCodes [258, 160, 66, 18, 8, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 361), (160, 97), (66, 150), (18, 256), (8, 130), (6, 1), (1, 2)]
    (codeMat 241) (codeMat 396) (codeMat 106) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane365RankCoverGenSource0037 :
    QuotientRankAtLeast (spanCodes [256, 130, 34, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 63), (130, 40), (34, 11), (18, 8), (10, 208), (6, 2), (1, 128)]
    (codeMat 395) (codeMat 116) (codeMat 92) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit11_lb12

theorem plane365RankCoverGenSource0038 :
    QuotientRankAtLeast (spanCodes [256, 160, 96, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 3), (160, 29), (96, 28), (18, 360), (10, 352), (6, 384), (1, 256)]
    (codeMat 84) (codeMat 230) (codeMat 159) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane365RankCoverGenSource0039 :
    QuotientRankAtLeast (spanCodes [266, 128, 72, 32, 18, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(266, 501), (128, 384), (72, 3), (32, 360), (18, 256), (6, 8), (1, 1)]
    (codeMat 249) (codeMat 417) (codeMat 177) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
