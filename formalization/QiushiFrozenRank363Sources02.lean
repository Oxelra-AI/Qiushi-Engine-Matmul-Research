import QiushiFrozenRank363Data
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiPlane274GenBindings01
import QiushiStep81Qdim2Generated
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane363RankCoverGenSource0020 :
    QuotientRankAtLeast (spanCodes [262, 140, 72, 44, 20, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 80, 12, 2, 1] [(262, 350), (140, 242), (72, 1), (44, 259), (20, 252), (1, 3)]
    (codeMat 254) (codeMat 279) (codeMat 279) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.plane274GenBound0011

theorem plane363RankCoverGenSource0021 :
    QuotientRankAtLeast (spanCodes [262, 142, 64, 46, 20, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 80, 12, 2, 1] [(262, 83), (142, 92), (64, 1), (46, 429), (20, 350), (1, 3)]
    (codeMat 492) (codeMat 419) (codeMat 183) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.plane274GenBound0011

theorem plane363RankCoverGenSource0022 :
    QuotientRankAtLeast (spanCodes [260, 160, 64, 20, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 256), (160, 227), (64, 130), (20, 28), (12, 20), (2, 3), (1, 2)]
    (codeMat 337) (codeMat 282) (codeMat 267) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane363RankCoverGenSource0023 :
    QuotientRankAtLeast (spanCodes [258, 160, 66, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 30), (160, 245), (66, 23), (16, 360), (10, 149), (4, 3), (1, 2)]
    (codeMat 489) (codeMat 174) (codeMat 359) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane363RankCoverGenSource0024 :
    QuotientRankAtLeast (spanCodes [256, 160, 66, 18, 8, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 511), (160, 227), (66, 23), (18, 8), (8, 3), (6, 130), (1, 2)]
    (codeMat 395) (codeMat 309) (codeMat 309) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane363RankCoverGenSource0025 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 32, 18, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 9), (128, 8), (66, 80), (32, 63), (18, 40), (6, 2), (1, 128)]
    (codeMat 460) (codeMat 116) (codeMat 92) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit11_lb12

theorem plane363RankCoverGenSource0026 :
    QuotientRankAtLeast (spanCodes [262, 132, 68, 36, 20, 8, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 235), (132, 373), (68, 29), (36, 8), (20, 138), (8, 2), (1, 3)]
    (codeMat 467) (codeMat 179) (codeMat 421) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane363RankCoverGenSource0027 :
    QuotientRankAtLeast (spanCodes [262, 130, 68, 34, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(262, 52), (130, 32), (68, 402), (34, 11), (20, 10), (10, 208), (1, 128)]
    (codeMat 331) (codeMat 116) (codeMat 92) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.step81o17s4Span_lb

theorem plane363RankCoverGenSource0028 :
    QuotientRankAtLeast (spanCodes [262, 134, 66, 38, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 413), (134, 245), (66, 30), (38, 287), (20, 252), (10, 28), (1, 3)]
    (codeMat 247) (codeMat 279) (codeMat 279) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane363RankCoverGenSource0029 :
    QuotientRankAtLeast (spanCodes [262, 128, 64, 32, 20, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 387), (128, 3), (64, 2), (32, 360), (20, 413), (14, 278), (1, 130)]
    (codeMat 380) (codeMat 286) (codeMat 303) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
