import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiOrbit29FP
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0290 :
    QuotientRankAtLeast (spanCodes [275, 145, 66, 50, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(275, 116), (145, 29), (66, 235), (50, 104), (10, 232), (6, 8)]
    (codeMat 142) (codeMat 395) (codeMat 474) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0291 :
    QuotientRankAtLeast (spanCodes [275, 146, 66, 49, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(275, 159), (146, 130), (66, 235), (49, 28), (10, 227), (6, 3)]
    (codeMat 190) (codeMat 394) (codeMat 330) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0292 :
    QuotientRankAtLeast (spanCodes [273, 133, 81, 49, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(273, 171), (133, 69), (81, 170), (49, 176), (8, 16), (2, 320)]
    (codeMat 84) (codeMat 174) (codeMat 359) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane490GenSource0293 :
    QuotientRankAtLeast (spanCodes [274, 148, 66, 48, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(274, 150), (148, 20), (66, 105), (48, 128), (10, 96), (1, 8)]
    (codeMat 143) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0294 :
    QuotientRankAtLeast (spanCodes [274, 144, 112, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(274, 245), (144, 130), (112, 20), (10, 97), (6, 9), (1, 8)]
    (codeMat 177) (codeMat 426) (codeMat 335) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0295 :
    QuotientRankAtLeast (spanCodes [274, 162, 66, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(274, 252), (162, 255), (66, 186), (10, 184), (6, 24), (1, 16)]
    (codeMat 142) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane490GenSource0296 :
    QuotientRankAtLeast (spanCodes [274, 160, 64, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(274, 255), (160, 224), (64, 128), (10, 151), (6, 3), (1, 2)]
    (codeMat 305) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0297 :
    QuotientRankAtLeast (spanCodes [274, 160, 66, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(274, 118), (160, 255), (66, 149), (10, 150), (4, 128), (1, 2)]
    (codeMat 143) (codeMat 403) (codeMat 403) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0298 :
    QuotientRankAtLeast (spanCodes [259, 128, 66, 34, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 252), (128, 3), (66, 28), (34, 148), (16, 2), (10, 20)]
    (codeMat 86) (codeMat 298) (codeMat 270) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0299 :
    QuotientRankAtLeast (spanCodes [258, 129, 71, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 252), (129, 227), (71, 255), (39, 104), (17, 97), (10, 105)]
    (codeMat 115) (codeMat 491) (codeMat 375) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
