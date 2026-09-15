import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiOrbit29FP
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit220Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0400 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 34, 20, 9]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(257, 68), (129, 70), (64, 1), (34, 160), (20, 176), (9, 8)]
    (codeMat 92) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane491GenSource0401 :
    QuotientRankAtLeast (spanCodes [257, 134, 71, 37, 19, 9]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 224), (134, 255), (71, 28), (37, 96), (19, 105), (9, 8)]
    (codeMat 123) (codeMat 410) (codeMat 331) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0402 :
    QuotientRankAtLeast (spanCodes [257, 147, 82, 48, 9, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 224), (147, 246), (82, 30), (48, 130), (9, 3), (6, 128)]
    (codeMat 99) (codeMat 409) (codeMat 473) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0403 :
    QuotientRankAtLeast (spanCodes [282, 128, 83, 35, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(282, 351), (128, 16), (83, 378), (35, 228), (7, 192)]
    (codeMat 103) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane491GenSource0404 :
    QuotientRankAtLeast (spanCodes [258, 128, 75, 35, 27, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 10), (128, 16), (75, 436), (35, 68), (27, 260), (4, 1)]
    (codeMat 161) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0405 :
    QuotientRankAtLeast (spanCodes [264, 129, 64, 34, 16, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(264, 170), (129, 160), (64, 16), (34, 69), (16, 260), (4, 320)]
    (codeMat 99) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0406 :
    QuotientRankAtLeast (spanCodes [257, 137, 65, 42, 17, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(257, 26), (137, 197), (65, 27), (42, 96), (17, 368), (4, 16)]
    (codeMat 204) (codeMat 171) (codeMat 485) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane491GenSource0407 :
    QuotientRankAtLeast (spanCodes [264, 129, 64, 34, 17, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(264, 238), (129, 228), (64, 27), (34, 176), (17, 480), (5, 320)]
    (codeMat 95) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0408 :
    QuotientRankAtLeast (spanCodes [258, 146, 81, 49, 8, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 447), (146, 1), (81, 26), (49, 176), (8, 16), (5, 320)]
    (codeMat 87) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0409 :
    QuotientRankAtLeast (spanCodes [257, 144, 84, 49, 12, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 246), (144, 2), (84, 125), (49, 96), (12, 232), (2, 128)]
    (codeMat 94) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
