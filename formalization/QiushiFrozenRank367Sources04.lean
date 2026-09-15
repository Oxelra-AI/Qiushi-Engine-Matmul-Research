import QiushiFrozenRank367Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane367RankCoverGenSource0040 :
    QuotientRankAtLeast (spanCodes [256, 160, 64, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (160, 68), (64, 2), (16, 256), (10, 160), (4, 8), (1, 16)]
    (codeMat 140) (codeMat 140) (codeMat 98) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit10_lb12

theorem plane367RankCoverGenSource0041 :
    QuotientRankAtLeast (spanCodes [266, 130, 72, 34, 16, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(266, 124), (130, 384), (72, 3), (34, 96), (16, 256), (4, 8), (1, 1)]
    (codeMat 185) (codeMat 161) (codeMat 161) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane367RankCoverGenSource0042 :
    QuotientRankAtLeast (spanCodes [266, 138, 72, 42, 16, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(266, 84), (138, 484), (72, 18), (42, 68), (16, 256), (4, 8), (1, 9)]
    (codeMat 177) (codeMat 169) (codeMat 225) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit10_lb12

theorem plane367RankCoverGenSource0043 :
    QuotientRankAtLeast (spanCodes [256, 130, 34, 18, 8, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(256, 365), (130, 260), (34, 13), (18, 4), (8, 18), (6, 8), (1, 16)]
    (codeMat 395) (codeMat 396) (codeMat 106) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_7

theorem plane367RankCoverGenSource0044 :
    QuotientRankAtLeast (spanCodes [256, 160, 98, 18, 8, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 511), (160, 284), (98, 157), (18, 130), (8, 3), (6, 8), (1, 1)]
    (codeMat 409) (codeMat 423) (codeMat 181) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane367RankCoverGenSource0045 :
    QuotientRankAtLeast (spanCodes [258, 160, 66, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 440), (160, 168), (66, 71), (18, 256), (10, 69), (6, 8), (1, 1)]
    (codeMat 241) (codeMat 417) (codeMat 177) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit10_lb12

theorem plane367RankCoverGenSource0046 :
    QuotientRankAtLeast (spanCodes [264, 128, 64, 32, 18, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(264, 149), (128, 128), (64, 2), (32, 360), (18, 256), (6, 8), (1, 1)]
    (codeMat 225) (codeMat 417) (codeMat 177) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane367RankCoverGenSource0047 :
    QuotientRankAtLeast (spanCodes [264, 128, 66, 32, 18, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(264, 413), (128, 384), (66, 118), (32, 360), (18, 256), (6, 8), (1, 9)]
    (codeMat 249) (codeMat 425) (codeMat 249) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane367RankCoverGenSource0048 :
    QuotientRankAtLeast (spanCodes [264, 136, 64, 40, 18, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(264, 245), (136, 252), (64, 27), (40, 432), (18, 256), (6, 8), (1, 24)]
    (codeMat 205) (codeMat 397) (codeMat 250) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit10_lb12

theorem plane367RankCoverGenSource0049 :
    QuotientRankAtLeast (spanCodes [264, 138, 64, 42, 18, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(264, 374), (138, 224), (64, 384), (42, 11), (18, 8), (6, 130), (1, 128)]
    (codeMat 331) (codeMat 372) (codeMat 93) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
