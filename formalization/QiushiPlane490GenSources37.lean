import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0370 :
    QuotientRankAtLeast (spanCodes [258, 131, 67, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 252), (131, 31), (67, 28), (39, 148), (17, 22), (10, 20)]
    (codeMat 95) (codeMat 314) (codeMat 271) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0371 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 104), (128, 8), (64, 9), (39, 148), (17, 20), (10, 22)]
    (codeMat 92) (codeMat 313) (codeMat 313) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0372 :
    QuotientRankAtLeast (spanCodes [258, 132, 71, 36, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 96), (132, 104), (71, 105), (36, 128), (17, 148), (10, 150)]
    (codeMat 93) (codeMat 473) (codeMat 409) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0373 :
    QuotientRankAtLeast (spanCodes [258, 135, 68, 36, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 224), (135, 252), (68, 255), (36, 128), (17, 148), (10, 150)]
    (codeMat 94) (codeMat 473) (codeMat 409) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0374 :
    QuotientRankAtLeast (spanCodes [275, 146, 81, 51, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(275, 177), (146, 27), (81, 287), (51, 176), (10, 480), (6, 16)]
    (codeMat 206) (codeMat 95) (codeMat 244) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane490GenSource0375 :
    QuotientRankAtLeast (spanCodes [275, 130, 81, 34, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(275, 156), (130, 3), (81, 29), (34, 224), (10, 232), (7, 128)]
    (codeMat 85) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0376 :
    QuotientRankAtLeast (spanCodes [258, 195, 35, 17, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 232), (195, 128), (35, 11), (17, 22), (10, 20), (7, 8)]
    (codeMat 331) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0377 :
    QuotientRankAtLeast (spanCodes [258, 195, 32, 17, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 104), (195, 128), (32, 9), (17, 20), (10, 22), (4, 8)]
    (codeMat 331) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0378 :
    QuotientRankAtLeast (spanCodes [259, 130, 97, 16, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 246), (130, 9), (97, 20), (16, 8), (10, 96), (5, 128)]
    (codeMat 87) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0379 :
    QuotientRankAtLeast (spanCodes [273, 148, 81, 49, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(273, 161), (148, 69), (81, 186), (49, 160), (8, 16), (2, 320)]
    (codeMat 86) (codeMat 142) (codeMat 354) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
