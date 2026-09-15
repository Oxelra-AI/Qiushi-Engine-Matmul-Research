import QiushiFrozenRank361Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane361RankCoverGenSource0060 :
    QuotientRankAtLeast (spanCodes [258, 136, 74, 40, 18, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 385), (136, 287), (74, 28), (40, 360), (18, 511), (6, 1), (1, 3)]
    (codeMat 377) (codeMat 443) (codeMat 254) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane361RankCoverGenSource0061 :
    QuotientRankAtLeast (spanCodes [256, 136, 72, 42, 18, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(256, 360), (136, 373), (72, 24), (42, 258), (18, 260), (6, 18), (1, 16)]
    (codeMat 207) (codeMat 426) (codeMat 335) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_7

theorem plane361RankCoverGenSource0062 :
    QuotientRankAtLeast (spanCodes [256, 138, 72, 42, 18, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 360), (138, 503), (72, 9), (42, 258), (18, 384), (6, 3), (1, 1)]
    (codeMat 249) (codeMat 405) (codeMat 407) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane361RankCoverGenSource0063 :
    QuotientRankAtLeast (spanCodes [256, 128, 70, 34, 20, 8, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 32), (128, 40), (70, 81), (34, 69), (20, 68), (8, 128), (1, 130)]
    (codeMat 163) (codeMat 394) (codeMat 330) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit11_lb12

theorem plane361RankCoverGenSource0064 :
    QuotientRankAtLeast (spanCodes [256, 130, 68, 32, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 256), (130, 9), (68, 96), (32, 384), (20, 374), (10, 413), (1, 360)]
    (codeMat 309) (codeMat 346) (codeMat 459) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane361RankCoverGenSource0065 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 32, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (132, 23), (68, 149), (32, 3), (20, 30), (10, 245), (1, 360)]
    (codeMat 486) (codeMat 94) (codeMat 500) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane361RankCoverGenSource0066 :
    QuotientRankAtLeast (spanCodes [258, 130, 70, 34, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 265), (130, 9), (70, 96), (34, 246), (20, 374), (10, 245), (1, 360)]
    (codeMat 317) (codeMat 382) (codeMat 499) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane361RankCoverGenSource0067 :
    QuotientRankAtLeast (spanCodes [258, 132, 70, 34, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 21), (132, 23), (70, 509), (34, 29), (20, 30), (10, 413), (1, 360)]
    (codeMat 494) (codeMat 122) (codeMat 460) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane361RankCoverGenSource0068 :
    QuotientRankAtLeast (spanCodes [260, 128, 64, 36, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 1), (128, 384), (64, 128), (36, 8), (20, 503), (10, 276), (1, 130)]
    (codeMat 285) (codeMat 156) (codeMat 102) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane361RankCoverGenSource0069 :
    QuotientRankAtLeast (spanCodes [260, 134, 64, 36, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 2), (134, 21), (64, 9), (36, 130), (20, 381), (10, 97), (1, 8)]
    (codeMat 397) (codeMat 163) (codeMat 165) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
