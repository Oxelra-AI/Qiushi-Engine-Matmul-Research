import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0350 :
    QuotientRankAtLeast (spanCodes [259, 130, 70, 33, 18, 11]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 150), (130, 1), (70, 149), (33, 232), (18, 8), (11, 96)]
    (codeMat 157) (codeMat 355) (codeMat 190) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0351 :
    QuotientRankAtLeast (spanCodes [260, 133, 70, 38, 18, 11]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(260, 128), (133, 20), (70, 150), (38, 96), (18, 8), (11, 105)]
    (codeMat 107) (codeMat 345) (codeMat 345) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0352 :
    QuotientRankAtLeast (spanCodes [258, 135, 66, 36, 22, 11]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 496), (135, 336), (66, 480), (36, 1), (22, 79), (11, 507)]
    (codeMat 355) (codeMat 159) (codeMat 230) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0353 :
    QuotientRankAtLeast (spanCodes [262, 129, 65, 34, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(262, 480), (129, 336), (65, 16), (34, 507), (21, 79), (10, 506)]
    (codeMat 298) (codeMat 190) (codeMat 355) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0354 :
    QuotientRankAtLeast (spanCodes [258, 133, 66, 38, 22, 9]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 436), (133, 78), (66, 437), (38, 176), (22, 160), (9, 320)]
    (codeMat 212) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0355 :
    QuotientRankAtLeast (spanCodes [259, 131, 67, 32, 23, 15]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 22), (131, 148), (67, 150), (32, 9), (23, 104), (15, 105)]
    (codeMat 98) (codeMat 253) (codeMat 415) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0356 :
    QuotientRankAtLeast (spanCodes [258, 135, 68, 36, 16, 13]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 506), (135, 437), (68, 436), (36, 16), (16, 320), (13, 176)]
    (codeMat 157) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0357 :
    QuotientRankAtLeast (spanCodes [263, 134, 64, 37, 20, 13]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(263, 170), (134, 463), (64, 260), (37, 283), (20, 127), (13, 475)]
    (codeMat 174) (codeMat 500) (codeMat 94) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane491GenSource0358 :
    QuotientRankAtLeast (spanCodes [256, 131, 67, 32, 23, 12]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 1), (131, 150), (67, 148), (32, 8), (23, 232), (12, 104)]
    (codeMat 212) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0359 :
    QuotientRankAtLeast (spanCodes [256, 148, 84, 52, 12, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 3), (148, 246), (84, 244), (52, 232), (12, 224), (3, 128)]
    (codeMat 84) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
