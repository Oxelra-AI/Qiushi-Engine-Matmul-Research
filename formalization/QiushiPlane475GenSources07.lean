import QiushiPlane475GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane475GenSource0070 :
    QuotientRankAtLeast (spanCodes [259, 146, 80, 48, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(259, 283), (146, 1), (80, 446), (48, 16), (10, 112), (7, 256)]
    (codeMat 87) (codeMat 110) (codeMat 444) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane475GenSource0071 :
    QuotientRankAtLeast (spanCodes [291, 160, 96, 19, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(291, 352), (160, 363), (96, 362), (19, 446), (10, 463), (5, 16)]
    (codeMat 460) (codeMat 477) (codeMat 431) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane475GenSource0072 :
    QuotientRankAtLeast (spanCodes [274, 130, 67, 35, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(274, 202), (130, 432), (67, 160), (35, 357), (10, 96), (4, 260)]
    (codeMat 99) (codeMat 468) (codeMat 87) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane475GenSource0073 :
    QuotientRankAtLeast (spanCodes [258, 133, 64, 32, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 496), (133, 160), (64, 320), (32, 1), (20, 78), (10, 437)]
    (codeMat 298) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane475GenSource0074 :
    QuotientRankAtLeast (spanCodes [258, 131, 70, 38, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 436), (131, 506), (70, 79), (38, 176), (18, 16), (10, 336)]
    (codeMat 157) (codeMat 345) (codeMat 345) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane475GenSource0075 :
    QuotientRankAtLeast (spanCodes [257, 129, 68, 36, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(257, 420), (129, 447), (68, 164), (36, 16), (19, 446), (10, 463)]
    (codeMat 351) (codeMat 106) (codeMat 396) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane475GenSource0076 :
    QuotientRankAtLeast (spanCodes [274, 129, 67, 35, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(274, 196), (129, 463), (67, 113), (35, 272), (10, 112), (7, 16)]
    (codeMat 207) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane475GenSource0077 :
    QuotientRankAtLeast (spanCodes [261, 128, 69, 37, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(261, 96), (128, 9), (69, 104), (37, 224), (23, 31), (10, 252)]
    (codeMat 116) (codeMat 346) (codeMat 459) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane475GenSource0078 :
    QuotientRankAtLeast (spanCodes [258, 128, 69, 37, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 126), (128, 9), (69, 245), (37, 232), (16, 8), (10, 96)]
    (codeMat 214) (codeMat 355) (codeMat 190) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane475GenSource0079 :
    QuotientRankAtLeast (spanCodes [261, 135, 66, 34, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(261, 252), (135, 28), (66, 227), (34, 104), (16, 8), (10, 97)]
    (codeMat 114) (codeMat 369) (codeMat 377) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
