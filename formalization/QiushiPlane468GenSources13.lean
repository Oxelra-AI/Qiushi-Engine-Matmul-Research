import QiushiPlane468GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane468GenSource0130 :
    QuotientRankAtLeast (spanCodes [259, 131, 69, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 224), (131, 227), (69, 255), (39, 96), (17, 97), (10, 105)]
    (codeMat 123) (codeMat 459) (codeMat 346) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane468GenSource0131 :
    QuotientRankAtLeast (spanCodes [258, 131, 68, 39, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(258, 378), (131, 170), (68, 21), (39, 356), (16, 260), (10, 357)]
    (codeMat 171) (codeMat 174) (codeMat 359) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane468GenSource0132 :
    QuotientRankAtLeast (spanCodes [274, 131, 83, 32, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(274, 462), (131, 191), (83, 170), (32, 1), (10, 453), (7, 192)]
    (codeMat 114) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane468GenSource0133 :
    QuotientRankAtLeast (spanCodes [273, 128, 83, 35, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(273, 212), (128, 27), (83, 197), (35, 272), (10, 368), (7, 16)]
    (codeMat 205) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane468GenSource0134 :
    QuotientRankAtLeast (spanCodes [258, 147, 82, 49, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(258, 368), (147, 453), (82, 21), (49, 283), (10, 191), (6, 192)]
    (codeMat 103) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane468GenSource0135 :
    QuotientRankAtLeast (spanCodes [274, 131, 82, 33, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(274, 20), (131, 246), (82, 29), (33, 96), (10, 232), (6, 128)]
    (codeMat 95) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane468GenSource0136 :
    QuotientRankAtLeast (spanCodes [263, 128, 65, 36, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(263, 496), (128, 320), (65, 16), (36, 1), (21, 437), (10, 506)]
    (codeMat 299) (codeMat 142) (codeMat 354) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane468GenSource0137 :
    QuotientRankAtLeast (spanCodes [262, 129, 65, 37, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(262, 191), (129, 283), (65, 256), (37, 97), (21, 113), (10, 479)]
    (codeMat 342) (codeMat 470) (codeMat 213) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane468GenSource0138 :
    QuotientRankAtLeast (spanCodes [257, 129, 70, 37, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(257, 507), (129, 506), (70, 79), (37, 480), (18, 16), (10, 336)]
    (codeMat 156) (codeMat 125) (codeMat 348) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane468GenSource0139 :
    QuotientRankAtLeast (spanCodes [263, 135, 70, 35, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(263, 436), (135, 437), (70, 79), (35, 176), (18, 320), (10, 336)]
    (codeMat 212) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
