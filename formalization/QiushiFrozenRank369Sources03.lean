import QiushiFrozenRank369Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit14FP
import QiushiStep81Qdim2Generated
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane369RankCoverGenSource0030 :
    QuotientRankAtLeast (spanCodes [262, 128, 64, 32, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 259), (128, 256), (64, 128), (32, 511), (20, 227), (10, 406), (1, 130)]
    (codeMat 285) (codeMat 428) (codeMat 107) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane369RankCoverGenSource0031 :
    QuotientRankAtLeast (spanCodes [262, 134, 64, 38, 20, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 276), (134, 406), (64, 128), (38, 235), (20, 414), (12, 246), (1, 384)]
    (codeMat 359) (codeMat 372) (codeMat 93) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane369RankCoverGenSource0032 :
    QuotientRankAtLeast (spanCodes [258, 128, 68, 32, 20, 14, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 101), (128, 360), (68, 300), (32, 390), (20, 180), (14, 20), (1, 32)]
    (codeMat 93) (codeMat 412) (codeMat 111) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.step81o17s4Span_lb

theorem plane369RankCoverGenSource0033 :
    QuotientRankAtLeast (spanCodes [262, 130, 64, 34, 20, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 31), (130, 3), (64, 9), (34, 480), (20, 224), (14, 104), (1, 8)]
    (codeMat 205) (codeMat 311) (codeMat 307) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane369RankCoverGenSource0034 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 36, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 365), (132, 151), (68, 76), (36, 40), (20, 23), (8, 9), (2, 2), (1, 1)]
    (codeMat 409) (codeMat 277) (codeMat 277) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_3

theorem plane369RankCoverGenSource0035 :
    QuotientRankAtLeast (spanCodes [260, 132, 64, 36, 20, 12, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 504), (132, 149), (64, 219), (36, 63), (20, 23), (12, 31), (2, 2), (1, 3)]
    (codeMat 465) (codeMat 317) (codeMat 285) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_3

theorem plane369RankCoverGenSource0036 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 34, 16, 8, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 219), (130, 288), (66, 77), (34, 28), (16, 32), (8, 8), (4, 3), (1, 1)]
    (codeMat 465) (codeMat 165) (codeMat 163) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
