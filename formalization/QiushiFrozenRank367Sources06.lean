import QiushiFrozenRank367Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane367RankCoverGenSource0060 :
    QuotientRankAtLeast (spanCodes [256, 128, 70, 32, 20, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (128, 8), (70, 118), (32, 3), (20, 30), (14, 246), (1, 384)]
    (codeMat 500) (codeMat 84) (codeMat 84) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane367RankCoverGenSource0061 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 36, 20, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (132, 150), (64, 128), (36, 1), (20, 361), (14, 96), (1, 256)]
    (codeMat 99) (codeMat 214) (codeMat 214) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane367RankCoverGenSource0062 :
    QuotientRankAtLeast (spanCodes [256, 128, 32, 16, 8, 4, 2, 1]) 3 := by
  apply quotientRankAtLeast_weaken (n := 3) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [128, 64, 32, 16, 8, 4, 2, 1] [(256, 32), (128, 4), (32, 16), (16, 2), (8, 130), (4, 8), (2, 1), (1, 65)]
    (codeMat 273) (codeMat 99) (codeMat 172) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_1

theorem plane367RankCoverGenSource0063 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 32, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 256), (128, 130), (68, 69), (32, 32), (20, 20), (8, 8), (2, 2), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_3

theorem plane367RankCoverGenSource0064 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 36, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 288), (132, 150), (68, 77), (36, 32), (20, 22), (8, 9), (2, 2), (1, 1)]
    (codeMat 409) (codeMat 273) (codeMat 273) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_3

theorem plane367RankCoverGenSource0065 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 20, 12, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 256), (128, 128), (68, 196), (32, 32), (20, 20), (12, 28), (2, 2), (1, 3)]
    (codeMat 273) (codeMat 281) (codeMat 281) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_3

theorem plane367RankCoverGenSource0066 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 36, 20, 12, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 288), (132, 148), (64, 216), (36, 32), (20, 22), (12, 31), (2, 2), (1, 3)]
    (codeMat 473) (codeMat 281) (codeMat 281) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_3

theorem plane367RankCoverGenSource0067 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 34, 16, 8, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 150), (130, 288), (66, 77), (34, 20), (16, 32), (8, 8), (4, 2), (1, 1)]
    (codeMat 465) (codeMat 161) (codeMat 161) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_3

theorem plane367RankCoverGenSource0068 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 32, 18, 8, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 384), (128, 256), (66, 68), (32, 54), (18, 32), (8, 9), (6, 2), (1, 1)]
    (codeMat 281) (codeMat 417) (codeMat 177) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_3

theorem plane367RankCoverGenSource0069 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 32, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 436), (128, 288), (64, 216), (32, 54), (18, 32), (10, 31), (6, 2), (1, 3)]
    (codeMat 473) (codeMat 425) (codeMat 249) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
