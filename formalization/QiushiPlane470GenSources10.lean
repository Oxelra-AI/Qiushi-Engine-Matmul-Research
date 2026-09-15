import QiushiPlane470GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit112From35T
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiWcOrbit141Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane470GenSource0100 :
    QuotientRankAtLeast (spanCodes [259, 131, 84, 48, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(259, 119), (131, 118), (84, 298), (48, 2), (10, 383)]
    (codeMat 468) (codeMat 498) (codeMat 206) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

theorem plane470GenSource0101 :
    QuotientRankAtLeast (spanCodes [259, 144, 84, 35, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(259, 264), (144, 2), (84, 298), (35, 265), (10, 383)]
    (codeMat 110) (codeMat 93) (codeMat 372) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

theorem plane470GenSource0102 :
    QuotientRankAtLeast (spanCodes [259, 128, 65, 38, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(259, 464), (128, 384), (65, 288), (38, 463), (21, 414), (10, 308)]
    (codeMat 270) (codeMat 500) (codeMat 94) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit76_lb15_unconditional

theorem plane470GenSource0103 :
    QuotientRankAtLeast (spanCodes [256, 160, 68, 16, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(256, 16), (160, 10), (68, 160), (16, 1), (9, 260), (3, 320)]
    (codeMat 98) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane470GenSource0104 :
    QuotientRankAtLeast (spanCodes [258, 162, 68, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 506), (162, 170), (68, 79), (16, 16), (10, 10), (1, 1)]
    (codeMat 401) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane470GenSource0105 :
    QuotientRankAtLeast (spanCodes [259, 130, 67, 33, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(259, 378), (130, 432), (67, 126), (33, 356), (23, 420), (10, 127)]
    (codeMat 247) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane470GenSource0106 :
    QuotientRankAtLeast (spanCodes [259, 129, 69, 36, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 31), (129, 224), (69, 252), (36, 9), (17, 96), (10, 104)]
    (codeMat 115) (codeMat 236) (codeMat 123) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane470GenSource0107 :
    QuotientRankAtLeast (spanCodes [259, 134, 69, 35, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 139), (134, 252), (69, 245), (35, 136), (17, 104), (10, 96)]
    (codeMat 158) (codeMat 229) (codeMat 187) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane470GenSource0108 :
    QuotientRankAtLeast (spanCodes [259, 131, 70, 37, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(259, 203), (131, 202), (70, 11), (37, 420), (18, 432), (10, 180)]
    (codeMat 140) (codeMat 445) (codeMat 478) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane470GenSource0109 :
    QuotientRankAtLeast (spanCodes [259, 133, 84, 48, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 8, 2, 1] [(259, 371), (133, 368), (84, 107), (48, 2), (10, 274)]
    (codeMat 215) (codeMat 461) (codeMat 234) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit112_lb15_mono

end QiushiMatmul
