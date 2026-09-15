import QiushiFrozenRank368Data
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiPlane315GenBindings01
import QiushiStep81Qdim2Generated
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane368RankCoverGenSource0020 :
    QuotientRankAtLeast (spanCodes [268, 128, 78, 32, 20, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(268, 272), (128, 1), (78, 283), (32, 432), (20, 222), (1, 192)]
    (codeMat 492) (codeMat 354) (codeMat 142) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.plane315GenBound0017

theorem plane368RankCoverGenSource0021 :
    QuotientRankAtLeast (spanCodes [264, 132, 72, 36, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(264, 418), (132, 76), (72, 18), (36, 256), (20, 69), (2, 1), (1, 2)]
    (codeMat 249) (codeMat 266) (codeMat 266) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit10_lb12

theorem plane368RankCoverGenSource0022 :
    QuotientRankAtLeast (spanCodes [266, 138, 72, 42, 16, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(266, 84), (138, 484), (72, 24), (42, 68), (16, 256), (4, 2), (1, 3)]
    (codeMat 177) (codeMat 169) (codeMat 225) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit10_lb12

theorem plane368RankCoverGenSource0023 :
    QuotientRankAtLeast (spanCodes [322, 128, 32, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(322, 61), (128, 40), (32, 219), (18, 8), (10, 208), (6, 130), (1, 128)]
    (codeMat 459) (codeMat 372) (codeMat 93) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit11_lb12

theorem plane368RankCoverGenSource0024 :
    QuotientRankAtLeast (spanCodes [262, 130, 68, 34, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(262, 312), (130, 32), (68, 295), (34, 80), (20, 208), (10, 81), (1, 219)]
    (codeMat 346) (codeMat 377) (codeMat 369) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.step81o17s4Span_lb

end QiushiMatmul
