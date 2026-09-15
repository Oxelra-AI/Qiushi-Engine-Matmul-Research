import QiushiFrozenRank361Data
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiPlane152GenBindings00
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane361RankCoverGenSource0040 :
    QuotientRankAtLeast (spanCodes [260, 134, 74, 46, 20, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(260, 256), (134, 164), (74, 26), (46, 362), (20, 191), (1, 16)]
    (codeMat 334) (codeMat 282) (codeMat 267) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.plane152GenBound0001

theorem plane361RankCoverGenSource0041 :
    QuotientRankAtLeast (spanCodes [292, 128, 100, 20, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(292, 360), (128, 128), (100, 232), (20, 23), (12, 30), (2, 2), (1, 3)]
    (codeMat 281) (codeMat 285) (codeMat 317) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane361RankCoverGenSource0042 :
    QuotientRankAtLeast (spanCodes [292, 132, 100, 20, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(292, 256), (132, 150), (100, 255), (20, 20), (12, 28), (2, 2), (1, 3)]
    (codeMat 465) (codeMat 281) (codeMat 281) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane361RankCoverGenSource0043 :
    QuotientRankAtLeast (spanCodes [264, 132, 68, 32, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(264, 245), (132, 23), (68, 30), (32, 360), (20, 149), (2, 2), (1, 3)]
    (codeMat 489) (codeMat 285) (codeMat 317) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane361RankCoverGenSource0044 :
    QuotientRankAtLeast (spanCodes [268, 128, 64, 36, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(268, 168), (128, 3), (64, 24), (36, 256), (20, 69), (2, 1), (1, 8)]
    (codeMat 233) (codeMat 266) (codeMat 266) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit10_lb12

theorem plane361RankCoverGenSource0045 :
    QuotientRankAtLeast (spanCodes [268, 132, 64, 36, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(268, 97), (132, 23), (64, 9), (36, 360), (20, 151), (2, 2), (1, 1)]
    (codeMat 425) (codeMat 277) (codeMat 277) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane361RankCoverGenSource0046 :
    QuotientRankAtLeast (spanCodes [268, 136, 64, 36, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(268, 148), (136, 28), (64, 3), (36, 360), (20, 104), (2, 8), (1, 1)]
    (codeMat 169) (codeMat 305) (codeMat 305) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane361RankCoverGenSource0047 :
    QuotientRankAtLeast (spanCodes [256, 140, 76, 40, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 3), (140, 372), (76, 374), (40, 360), (20, 480), (2, 256), (1, 384)]
    (codeMat 92) (codeMat 236) (codeMat 123) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane361RankCoverGenSource0048 :
    QuotientRankAtLeast (spanCodes [260, 128, 72, 44, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 256), (128, 130), (72, 8), (44, 361), (20, 150), (2, 2), (1, 1)]
    (codeMat 369) (codeMat 273) (codeMat 273) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane361RankCoverGenSource0049 :
    QuotientRankAtLeast (spanCodes [260, 132, 72, 44, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 432), (132, 79), (72, 16), (44, 264), (20, 77), (2, 1), (1, 8)]
    (codeMat 241) (codeMat 298) (codeMat 270) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
