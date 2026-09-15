import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit220Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0370 :
    QuotientRankAtLeast (spanCodes [256, 131, 67, 32, 23, 11]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 1), (131, 104), (67, 96), (32, 3), (23, 252), (11, 224)]
    (codeMat 116) (codeMat 212) (codeMat 86) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0371 :
    QuotientRankAtLeast (spanCodes [258, 128, 73, 35, 25, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 10), (128, 16), (73, 260), (35, 78), (25, 436), (4, 1)]
    (codeMat 417) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0372 :
    QuotientRankAtLeast (spanCodes [265, 137, 75, 42, 26, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(265, 126), (137, 252), (75, 31), (42, 96), (26, 224), (5, 8)]
    (codeMat 142) (codeMat 489) (codeMat 241) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0373 :
    QuotientRankAtLeast (spanCodes [267, 138, 74, 41, 27, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(267, 124), (138, 151), (74, 21), (41, 96), (27, 128), (5, 8)]
    (codeMat 207) (codeMat 467) (codeMat 339) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0374 :
    QuotientRankAtLeast (spanCodes [258, 146, 83, 49, 8, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 507), (146, 27), (83, 430), (49, 261), (8, 320), (7, 1)]
    (codeMat 177) (codeMat 375) (codeMat 491) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0375 :
    QuotientRankAtLeast (spanCodes [256, 146, 83, 49, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(256, 260), (146, 1), (83, 447), (49, 336), (10, 496), (7, 16)]
    (codeMat 207) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0376 :
    QuotientRankAtLeast (spanCodes [290, 163, 64, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(290, 368), (163, 379), (64, 1), (19, 446), (10, 113), (7, 16)]
    (codeMat 396) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane491GenSource0377 :
    QuotientRankAtLeast (spanCodes [273, 130, 83, 33, 11, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(273, 156), (130, 3), (83, 29), (33, 96), (11, 232), (7, 128)]
    (codeMat 93) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0378 :
    QuotientRankAtLeast (spanCodes [268, 138, 76, 41, 24]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(268, 53), (138, 52), (76, 245), (41, 414), (24, 16)]
    (codeMat 277) (codeMat 460) (codeMat 122) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane491GenSource0379 :
    QuotientRankAtLeast (spanCodes [260, 131, 65, 32, 21, 12]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(260, 1), (131, 104), (65, 8), (32, 3), (21, 252), (12, 28)]
    (codeMat 125) (codeMat 156) (codeMat 102) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
