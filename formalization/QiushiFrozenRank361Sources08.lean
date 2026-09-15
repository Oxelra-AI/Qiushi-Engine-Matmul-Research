import QiushiFrozenRank361Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane361RankCoverGenSource0080 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 36, 20, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (132, 150), (64, 128), (36, 1), (20, 361), (14, 96), (1, 256)]
    (codeMat 99) (codeMat 214) (codeMat 214) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane361RankCoverGenSource0081 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 36, 20, 12, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 256), (132, 196), (64, 128), (36, 32), (20, 31), (12, 22), (2, 3), (1, 2)]
    (codeMat 281) (codeMat 282) (codeMat 267) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_3

theorem plane361RankCoverGenSource0082 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 32, 18, 8, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 240), (128, 384), (66, 112), (32, 3), (18, 54), (8, 1), (6, 40), (1, 8)]
    (codeMat 266) (codeMat 181) (codeMat 423) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_3

theorem plane361RankCoverGenSource0083 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 32, 18, 8, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 243), (130, 438), (66, 113), (32, 3), (18, 54), (8, 1), (6, 40), (1, 8)]
    (codeMat 394) (codeMat 181) (codeMat 423) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_3

theorem plane361RankCoverGenSource0084 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 32, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 130), (128, 455), (66, 316), (32, 2), (18, 63), (10, 60), (6, 40), (1, 32)]
    (codeMat 394) (codeMat 242) (codeMat 205) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_3

theorem plane361RankCoverGenSource0085 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 34, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 392), (128, 504), (64, 288), (34, 62), (18, 63), (10, 60), (6, 8), (1, 32)]
    (codeMat 330) (codeMat 498) (codeMat 206) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
