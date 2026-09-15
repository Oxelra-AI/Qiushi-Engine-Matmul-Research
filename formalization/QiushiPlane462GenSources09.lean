import QiushiPlane462GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit72Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane462GenSource0090 :
    QuotientRankAtLeast (spanCodes [263, 129, 68, 33, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(263, 344), (129, 376), (68, 80), (33, 91), (18, 63), (10, 338)]
    (codeMat 110) (codeMat 190) (codeMat 355) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane462GenSource0091 :
    QuotientRankAtLeast (spanCodes [256, 135, 68, 36, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 8), (135, 232), (68, 104), (36, 1), (17, 150), (10, 148)]
    (codeMat 355) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane462GenSource0092 :
    QuotientRankAtLeast (spanCodes [259, 132, 68, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 31), (132, 252), (68, 255), (39, 22), (17, 148), (10, 150)]
    (codeMat 95) (codeMat 253) (codeMat 415) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane462GenSource0093 :
    QuotientRankAtLeast (spanCodes [261, 130, 68, 33, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(261, 363), (130, 1), (68, 437), (33, 368), (17, 352), (10, 96)]
    (codeMat 213) (codeMat 103) (codeMat 188) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane462GenSource0094 :
    QuotientRankAtLeast (spanCodes [260, 131, 68, 33, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 16), (131, 496), (68, 336), (33, 506), (16, 1), (10, 79)]
    (codeMat 298) (codeMat 107) (codeMat 428) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane462GenSource0095 :
    QuotientRankAtLeast (spanCodes [276, 146, 68, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(276, 26), (146, 1), (68, 420), (32, 16), (10, 96), (1, 256)]
    (codeMat 87) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane462GenSource0096 :
    QuotientRankAtLeast (spanCodes [304, 178, 64, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(304, 224), (178, 104), (64, 3), (10, 148), (4, 128), (1, 2)]
    (codeMat 141) (codeMat 401) (codeMat 401) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane462GenSource0097 :
    QuotientRankAtLeast (spanCodes [306, 178, 66, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(306, 127), (178, 119), (66, 23), (10, 151), (6, 1), (1, 2)]
    (codeMat 417) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane462GenSource0098 :
    QuotientRankAtLeast (spanCodes [258, 134, 68, 32, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(258, 332), (134, 101), (68, 278), (32, 32), (20, 264), (10, 344)]
    (codeMat 214) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane462GenSource0099 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 8), (132, 104), (68, 105), (39, 20), (17, 148), (10, 150)]
    (codeMat 92) (codeMat 249) (codeMat 425) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
