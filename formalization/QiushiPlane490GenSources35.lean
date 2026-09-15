import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiOrbit29FP
import QiushiOrbit35FP
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit220Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0350 :
    QuotientRankAtLeast (spanCodes [275, 146, 83, 51, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(275, 187), (146, 1), (83, 447), (51, 160), (10, 496), (6, 16)]
    (codeMat 207) (codeMat 111) (codeMat 412) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane490GenSource0351 :
    QuotientRankAtLeast (spanCodes [275, 146, 65, 33, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(275, 286), (146, 27), (65, 260), (33, 176), (10, 480), (6, 320)]
    (codeMat 92) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane490GenSource0352 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 36, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 96), (128, 8), (64, 9), (36, 128), (17, 20), (10, 22)]
    (codeMat 92) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0353 :
    QuotientRankAtLeast (spanCodes [258, 131, 67, 36, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 224), (131, 28), (67, 31), (36, 128), (17, 20), (10, 22)]
    (codeMat 95) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0354 :
    QuotientRankAtLeast (spanCodes [258, 132, 71, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(258, 68), (132, 69), (71, 71), (39, 160), (17, 168), (10, 184)]
    (codeMat 93) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane490GenSource0355 :
    QuotientRankAtLeast (spanCodes [256, 128, 102, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(256, 2), (128, 1), (102, 84), (19, 462), (10, 441)]
    (codeMat 380) (codeMat 107) (codeMat 428) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane490GenSource0356 :
    QuotientRankAtLeast (spanCodes [256, 195, 37, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(256, 16), (195, 192), (37, 378), (19, 350), (10, 245)]
    (codeMat 359) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane490GenSource0357 :
    QuotientRankAtLeast (spanCodes [256, 162, 65, 19, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(256, 27), (162, 197), (65, 1), (19, 446), (10, 113), (5, 16)]
    (codeMat 461) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane490GenSource0358 :
    QuotientRankAtLeast (spanCodes [258, 192, 32, 17, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 96), (192, 128), (32, 9), (17, 20), (10, 22), (4, 8)]
    (codeMat 267) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0359 :
    QuotientRankAtLeast (spanCodes [258, 192, 35, 17, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 224), (192, 128), (35, 11), (17, 20), (10, 22), (7, 8)]
    (codeMat 267) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
