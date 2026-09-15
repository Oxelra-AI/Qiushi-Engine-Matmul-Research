import QiushiPlane458GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit187Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane458GenSource0100 :
    QuotientRankAtLeast (spanCodes [289, 129, 96, 20, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(289, 430), (129, 462), (96, 97), (20, 272), (8, 260), (2, 432)]
    (codeMat 156) (codeMat 241) (codeMat 489) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane458GenSource0101 :
    QuotientRankAtLeast (spanCodes [289, 133, 100, 20, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(289, 430), (133, 26), (100, 437), (20, 176), (8, 320), (2, 16)]
    (codeMat 140) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane458GenSource0102 :
    QuotientRankAtLeast (spanCodes [291, 131, 98, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(291, 223), (131, 96), (98, 442), (17, 160), (10, 272), (5, 260)]
    (codeMat 85) (codeMat 428) (codeMat 107) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane458GenSource0103 :
    QuotientRankAtLeast (spanCodes [288, 226, 18, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(288, 32), (226, 397), (18, 390), (10, 391), (6, 128)]
    (codeMat 114) (codeMat 473) (codeMat 409) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane458GenSource0104 :
    QuotientRankAtLeast (spanCodes [289, 130, 97, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(289, 368), (130, 1), (97, 363), (19, 113), (10, 446), (7, 16)]
    (codeMat 397) (codeMat 334) (codeMat 442) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane458GenSource0105 :
    QuotientRankAtLeast (spanCodes [259, 134, 71, 36, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(259, 367), (134, 453), (71, 378), (36, 1), (20, 261), (10, 356)]
    (codeMat 163) (codeMat 141) (codeMat 226) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane458GenSource0106 :
    QuotientRankAtLeast (spanCodes [259, 129, 64, 36, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(259, 437), (129, 79), (64, 1), (36, 320), (20, 336), (10, 496)]
    (codeMat 212) (codeMat 407) (codeMat 405) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane458GenSource0107 :
    QuotientRankAtLeast (spanCodes [260, 128, 70, 35, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(260, 260), (128, 432), (70, 420), (35, 453), (20, 378), (10, 367)]
    (codeMat 334) (codeMat 477) (codeMat 431) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane458GenSource0108 :
    QuotientRankAtLeast (spanCodes [262, 133, 65, 34, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(262, 353), (133, 469), (65, 27), (34, 352), (20, 96), (10, 368)]
    (codeMat 215) (codeMat 143) (codeMat 482) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane458GenSource0109 :
    QuotientRankAtLeast (spanCodes [288, 128, 98, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(288, 2), (128, 9), (98, 116), (16, 8), (10, 96), (4, 128)]
    (codeMat 86) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
