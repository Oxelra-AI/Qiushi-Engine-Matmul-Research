import QiushiFrozenRank367Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane367RankCoverGenSource0030 :
    QuotientRankAtLeast (spanCodes [256, 160, 16, 8, 4, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(256, 256), (160, 96), (16, 8), (8, 24), (4, 4), (2, 1), (1, 3)]
    (codeMat 273) (codeMat 267) (codeMat 282) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_7

theorem plane367RankCoverGenSource0031 :
    QuotientRankAtLeast (spanCodes [260, 160, 96, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 256), (160, 227), (96, 97), (20, 28), (8, 8), (2, 3), (1, 1)]
    (codeMat 337) (codeMat 275) (codeMat 275) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane367RankCoverGenSource0032 :
    QuotientRankAtLeast (spanCodes [260, 160, 100, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 360), (160, 246), (100, 97), (20, 30), (8, 9), (2, 3), (1, 1)]
    (codeMat 409) (codeMat 279) (codeMat 279) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane367RankCoverGenSource0033 :
    QuotientRankAtLeast (spanCodes [256, 160, 64, 20, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 256), (160, 224), (64, 128), (20, 28), (12, 20), (2, 3), (1, 2)]
    (codeMat 273) (codeMat 282) (codeMat 267) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane367RankCoverGenSource0034 :
    QuotientRankAtLeast (spanCodes [268, 128, 64, 32, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(268, 228), (128, 8), (64, 24), (32, 256), (20, 68), (2, 1), (1, 3)]
    (codeMat 161) (codeMat 267) (codeMat 282) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit10_lb12

theorem plane367RankCoverGenSource0035 :
    QuotientRankAtLeast (spanCodes [268, 128, 72, 32, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(268, 264), (128, 3), (72, 384), (32, 360), (20, 149), (2, 2), (1, 128)]
    (codeMat 461) (codeMat 354) (codeMat 142) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane367RankCoverGenSource0036 :
    QuotientRankAtLeast (spanCodes [268, 132, 72, 36, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(268, 487), (132, 76), (72, 27), (36, 256), (20, 69), (2, 1), (1, 3)]
    (codeMat 249) (codeMat 267) (codeMat 282) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit10_lb12

theorem plane367RankCoverGenSource0037 :
    QuotientRankAtLeast (spanCodes [268, 136, 64, 40, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(268, 151), (136, 29), (64, 3), (40, 360), (20, 97), (2, 8), (1, 1)]
    (codeMat 233) (codeMat 309) (codeMat 309) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane367RankCoverGenSource0038 :
    QuotientRankAtLeast (spanCodes [258, 128, 32, 16, 8, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(258, 96), (128, 256), (32, 1), (16, 4), (8, 2), (4, 8), (1, 16)]
    (codeMat 266) (codeMat 140) (codeMat 98) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_7

theorem plane367RankCoverGenSource0039 :
    QuotientRankAtLeast (spanCodes [258, 160, 96, 16, 8, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 97), (160, 276), (96, 20), (16, 130), (8, 2), (4, 8), (1, 1)]
    (codeMat 273) (codeMat 163) (codeMat 165) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
