import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit72Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0410 :
    QuotientRankAtLeast (spanCodes [272, 136, 81, 41, 5, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 252), (136, 227), (81, 105), (41, 150), (5, 2), (2, 130)]
    (codeMat 143) (codeMat 491) (codeMat 375) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0411 :
    QuotientRankAtLeast (spanCodes [261, 132, 72, 36, 28, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(261, 97), (132, 446), (72, 256), (36, 1), (28, 26), (3, 16)]
    (codeMat 395) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane491GenSource0412 :
    QuotientRankAtLeast (spanCodes [264, 129, 64, 33, 20, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(264, 78), (129, 68), (64, 1), (33, 496), (20, 160), (3, 320)]
    (codeMat 92) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0413 :
    QuotientRankAtLeast (spanCodes [272, 136, 81, 40, 5, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 96), (136, 232), (81, 246), (40, 128), (5, 2), (3, 3)]
    (codeMat 177) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0414 :
    QuotientRankAtLeast (spanCodes [273, 137, 81, 41, 5, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(273, 254), (137, 118), (81, 126), (41, 150), (5, 2), (3, 1)]
    (codeMat 305) (codeMat 474) (codeMat 395) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0415 :
    QuotientRankAtLeast (spanCodes [263, 131, 67, 32, 23, 15]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(263, 136), (131, 104), (67, 96), (32, 3), (23, 148), (15, 149)]
    (codeMat 354) (codeMat 229) (codeMat 187) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0416 :
    QuotientRankAtLeast (spanCodes [258, 133, 65, 38, 21, 14]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 507), (133, 436), (65, 1), (38, 480), (21, 176), (14, 496)]
    (codeMat 213) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0417 :
    QuotientRankAtLeast (spanCodes [263, 132, 71, 39, 19, 12]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(263, 265), (132, 91), (71, 310), (39, 264), (19, 344), (12, 112)]
    (codeMat 86) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane491GenSource0418 :
    QuotientRankAtLeast (spanCodes [263, 135, 66, 36, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(263, 490), (135, 238), (66, 497), (36, 16), (22, 160), (10, 496)]
    (codeMat 158) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0419 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 35, 20, 9]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 148), (128, 128), (64, 2), (35, 252), (20, 224), (9, 3)]
    (codeMat 103) (codeMat 417) (codeMat 177) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
