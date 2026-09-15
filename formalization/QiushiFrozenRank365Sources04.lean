import QiushiFrozenRank365Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane365RankCoverGenSource0040 :
    QuotientRankAtLeast (spanCodes [266, 130, 66, 34, 18, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(266, 285), (130, 256), (66, 104), (34, 131), (18, 128), (6, 1), (1, 8)]
    (codeMat 345) (codeMat 396) (codeMat 106) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane365RankCoverGenSource0041 :
    QuotientRankAtLeast (spanCodes [266, 138, 66, 42, 18, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(266, 234), (138, 227), (66, 31), (42, 386), (18, 256), (6, 1), (1, 3)]
    (codeMat 233) (codeMat 397) (codeMat 250) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane365RankCoverGenSource0042 :
    QuotientRankAtLeast (spanCodes [258, 132, 68, 36, 20, 8, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 224), (132, 480), (68, 31), (36, 8), (20, 136), (8, 2), (1, 3)]
    (codeMat 339) (codeMat 177) (codeMat 417) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane365RankCoverGenSource0043 :
    QuotientRankAtLeast (spanCodes [256, 132, 66, 36, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 256), (132, 224), (66, 28), (36, 384), (20, 232), (10, 29), (1, 3)]
    (codeMat 318) (codeMat 273) (codeMat 273) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane365RankCoverGenSource0044 :
    QuotientRankAtLeast (spanCodes [260, 130, 70, 34, 20, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 40), (130, 32), (70, 208), (34, 109), (20, 100), (14, 210), (1, 128)]
    (codeMat 110) (codeMat 396) (codeMat 106) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit11_lb12

theorem plane365RankCoverGenSource0045 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 256), (128, 128), (68, 68), (32, 32), (20, 20), (8, 8), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_3

theorem plane365RankCoverGenSource0046 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 36, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 288), (132, 148), (68, 76), (36, 32), (20, 22), (8, 9), (2, 2), (1, 1)]
    (codeMat 473) (codeMat 273) (codeMat 273) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_3

theorem plane365RankCoverGenSource0047 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 32, 20, 12, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 256), (128, 130), (68, 199), (32, 32), (20, 20), (12, 28), (2, 2), (1, 3)]
    (codeMat 337) (codeMat 281) (codeMat 281) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_3

theorem plane365RankCoverGenSource0048 :
    QuotientRankAtLeast (spanCodes [260, 132, 64, 36, 20, 12, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 288), (132, 150), (64, 219), (36, 32), (20, 22), (12, 31), (2, 2), (1, 3)]
    (codeMat 409) (codeMat 281) (codeMat 281) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_3

theorem plane365RankCoverGenSource0049 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 32, 18, 8, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 436), (128, 288), (66, 76), (32, 54), (18, 32), (8, 9), (6, 2), (1, 1)]
    (codeMat 473) (codeMat 417) (codeMat 177) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
