import QiushiPlane487GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane487GenSource0350 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 36, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (128, 1), (68, 148), (36, 128), (16, 8), (10, 104)]
    (codeMat 212) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane487GenSource0351 :
    QuotientRankAtLeast (spanCodes [257, 130, 68, 39, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 150), (130, 1), (68, 148), (39, 232), (16, 8), (10, 104)]
    (codeMat 213) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane487GenSource0352 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 32, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (132, 20), (68, 148), (32, 1), (16, 8), (10, 104)]
    (codeMat 98) (codeMat 92) (codeMat 116) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane487GenSource0353 :
    QuotientRankAtLeast (spanCodes [257, 135, 68, 34, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 148), (135, 20), (68, 150), (34, 104), (16, 8), (10, 105)]
    (codeMat 106) (codeMat 377) (codeMat 369) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane487GenSource0354 :
    QuotientRankAtLeast (spanCodes [260, 133, 69, 36, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(260, 8), (133, 232), (69, 104), (36, 1), (17, 150), (10, 148)]
    (codeMat 299) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane487GenSource0355 :
    QuotientRankAtLeast (spanCodes [260, 134, 69, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(260, 8), (134, 104), (69, 105), (39, 20), (17, 148), (10, 150)]
    (codeMat 93) (codeMat 249) (codeMat 425) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane487GenSource0356 :
    QuotientRankAtLeast (spanCodes [256, 128, 80, 48, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (128, 3), (80, 28), (48, 8), (10, 224), (4, 128)]
    (codeMat 84) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane487GenSource0357 :
    QuotientRankAtLeast (spanCodes [257, 147, 80, 34, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(257, 462), (147, 30), (80, 31), (34, 272), (10, 20), (4, 432)]
    (codeMat 157) (codeMat 313) (codeMat 313) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane487GenSource0358 :
    QuotientRankAtLeast (spanCodes [274, 145, 81, 50, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(274, 507), (145, 447), (81, 446), (50, 480), (10, 496), (5, 320)]
    (codeMat 84) (codeMat 254) (codeMat 443) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane487GenSource0359 :
    QuotientRankAtLeast (spanCodes [273, 146, 82, 49, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(273, 270), (146, 260), (82, 276), (49, 78), (10, 436), (6, 1)]
    (codeMat 417) (codeMat 460) (codeMat 122) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
