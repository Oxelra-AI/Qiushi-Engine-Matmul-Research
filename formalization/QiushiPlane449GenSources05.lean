import QiushiPlane449GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiMonoOrbit149From65
import QiushiOrbit10FP
import QiushiStep99Mono3032
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane449GenSource0050 :
    QuotientRankAtLeast (spanCodes [272, 140, 78, 44, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 68, 16, 10, 1] [(272, 78), (140, 351), (78, 68), (44, 272), (1, 256)]
    (codeMat 94) (codeMat 498) (codeMat 206) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit149_lb15_mono

theorem plane449GenSource0051 :
    QuotientRankAtLeast (spanCodes [258, 144, 48, 8, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 68, 16, 8, 2, 1] [(258, 264), (144, 325), (48, 9), (8, 18), (6, 8), (1, 16)]
    (codeMat 331) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_mono_30_lb12

theorem plane449GenSource0052 :
    QuotientRankAtLeast (spanCodes [258, 130, 72, 34, 24, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 186), (130, 511), (72, 3), (34, 184), (24, 256), (4, 16), (1, 24)]
    (codeMat 142) (codeMat 187) (codeMat 229) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane449GenSource0053 :
    QuotientRankAtLeast (spanCodes [262, 128, 66, 32, 22, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(262, 326), (128, 325), (66, 68), (32, 432), (22, 424), (12, 160), (1, 256)]
    (codeMat 93) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane449GenSource0054 :
    QuotientRankAtLeast (spanCodes [288, 160, 64, 24, 4, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(288, 360), (160, 368), (64, 16), (24, 256), (4, 5), (2, 6), (1, 2)]
    (codeMat 161) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_7

theorem plane449GenSource0055 :
    QuotientRankAtLeast (spanCodes [260, 144, 64, 48, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(260, 360), (144, 24), (64, 7), (48, 256), (8, 4), (2, 16), (1, 2)]
    (codeMat 143) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_7

end QiushiMatmul
