import QiushiFrozenRank362Data
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane362RankCoverGenSource0020 :
    QuotientRankAtLeast (spanCodes [260, 132, 72, 44, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 432), (132, 79), (72, 16), (44, 264), (20, 77), (2, 1), (1, 8)]
    (codeMat 241) (codeMat 298) (codeMat 270) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit10_lb12

theorem plane362RankCoverGenSource0021 :
    QuotientRankAtLeast (spanCodes [290, 160, 98, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(290, 126), (160, 245), (98, 125), (16, 360), (10, 96), (4, 9), (1, 8)]
    (codeMat 233) (codeMat 188) (codeMat 103) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane362RankCoverGenSource0022 :
    QuotientRankAtLeast (spanCodes [290, 130, 96, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(290, 502), (130, 128), (96, 373), (18, 256), (10, 104), (6, 9), (1, 8)]
    (codeMat 233) (codeMat 428) (codeMat 107) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane362RankCoverGenSource0023 :
    QuotientRankAtLeast (spanCodes [264, 136, 64, 32, 18, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(264, 160), (136, 162), (64, 16), (32, 256), (18, 325), (6, 1), (1, 8)]
    (codeMat 161) (codeMat 394) (codeMat 330) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit10_lb12

theorem plane362RankCoverGenSource0024 :
    QuotientRankAtLeast (spanCodes [258, 134, 68, 34, 20, 8, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 373), (134, 414), (68, 105), (34, 29), (20, 30), (8, 9), (1, 8)]
    (codeMat 459) (codeMat 405) (codeMat 407) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane362RankCoverGenSource0025 :
    QuotientRankAtLeast (spanCodes [256, 134, 68, 34, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 511), (134, 383), (68, 149), (34, 246), (20, 374), (10, 245), (1, 360)]
    (codeMat 431) (codeMat 382) (codeMat 499) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane362RankCoverGenSource0026 :
    QuotientRankAtLeast (spanCodes [260, 132, 70, 32, 20, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 9), (132, 502), (70, 228), (32, 1), (20, 70), (12, 68), (1, 256)]
    (codeMat 122) (codeMat 212) (codeMat 86) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit10_lb12

theorem plane362RankCoverGenSource0027 :
    QuotientRankAtLeast (spanCodes [262, 128, 68, 34, 20, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 255), (128, 511), (68, 28), (34, 246), (20, 374), (12, 30), (1, 3)]
    (codeMat 375) (codeMat 183) (codeMat 419) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane362RankCoverGenSource0028 :
    QuotientRankAtLeast (spanCodes [258, 132, 64, 38, 20, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 29), (132, 30), (64, 9), (38, 373), (20, 414), (12, 97), (1, 8)]
    (codeMat 397) (codeMat 405) (codeMat 407) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane362RankCoverGenSource0029 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 36, 20, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 480), (128, 256), (66, 96), (36, 3), (20, 508), (14, 149), (1, 360)]
    (codeMat 299) (codeMat 229) (codeMat 187) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
