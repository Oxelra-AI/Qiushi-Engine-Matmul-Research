import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0420 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 34, 20, 9]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 128), (129, 148), (64, 2), (34, 96), (20, 104), (9, 1)]
    (codeMat 99) (codeMat 401) (codeMat 401) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0421 :
    QuotientRankAtLeast (spanCodes [263, 132, 67, 39, 23, 8]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(263, 31), (132, 252), (67, 224), (39, 22), (23, 148), (8, 128)]
    (codeMat 86) (codeMat 244) (codeMat 95) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0422 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 34, 20, 8]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 148), (129, 149), (64, 2), (34, 104), (20, 96), (8, 128)]
    (codeMat 156) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0423 :
    QuotientRankAtLeast (spanCodes [256, 131, 75, 32, 24, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 8), (131, 224), (75, 255), (32, 1), (24, 3), (7, 128)]
    (codeMat 98) (codeMat 205) (codeMat 242) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0424 :
    QuotientRankAtLeast (spanCodes [266, 137, 75, 42, 25, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(266, 99), (137, 126), (75, 139), (42, 227), (25, 252), (6, 3)]
    (codeMat 183) (codeMat 458) (codeMat 458) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0425 :
    QuotientRankAtLeast (spanCodes [267, 137, 74, 42, 24, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(267, 244), (137, 149), (74, 23), (42, 232), (24, 128), (6, 8)]
    (codeMat 143) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0426 :
    QuotientRankAtLeast (spanCodes [258, 138, 64, 41, 17, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 446), (138, 255), (64, 260), (41, 160), (17, 480), (5, 16)]
    (codeMat 142) (codeMat 498) (codeMat 206) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0427 :
    QuotientRankAtLeast (spanCodes [259, 138, 65, 41, 16, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(259, 446), (138, 69), (65, 260), (41, 160), (16, 320), (5, 16)]
    (codeMat 143) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0428 :
    QuotientRankAtLeast (spanCodes [275, 128, 81, 35, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(275, 171), (128, 320), (81, 238), (35, 507), (10, 437), (5, 1)]
    (codeMat 305) (codeMat 494) (codeMat 501) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0429 :
    QuotientRankAtLeast (spanCodes [269, 140, 73, 44, 29, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(269, 119), (140, 156), (73, 130), (44, 252), (29, 31), (3, 3)]
    (codeMat 190) (codeMat 481) (codeMat 185) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
