import QiushiPlane462GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit72Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane462GenSource0100 :
    QuotientRankAtLeast (spanCodes [259, 135, 68, 36, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 136), (135, 104), (68, 232), (36, 3), (17, 148), (10, 150)]
    (codeMat 355) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane462GenSource0101 :
    QuotientRankAtLeast (spanCodes [261, 129, 68, 34, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(261, 175), (129, 353), (68, 469), (34, 112), (17, 352), (10, 96)]
    (codeMat 214) (codeMat 359) (codeMat 174) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane462GenSource0102 :
    QuotientRankAtLeast (spanCodes [257, 132, 68, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 104), (132, 224), (68, 96), (39, 148), (17, 151), (10, 149)]
    (codeMat 299) (codeMat 467) (codeMat 339) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane462GenSource0103 :
    QuotientRankAtLeast (spanCodes [258, 135, 68, 36, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 224), (135, 252), (68, 255), (36, 128), (17, 148), (10, 150)]
    (codeMat 94) (codeMat 473) (codeMat 409) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane462GenSource0104 :
    QuotientRankAtLeast (spanCodes [261, 128, 68, 35, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(261, 222), (128, 1), (68, 437), (35, 272), (17, 352), (10, 96)]
    (codeMat 212) (codeMat 355) (codeMat 190) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane462GenSource0105 :
    QuotientRankAtLeast (spanCodes [260, 129, 68, 35, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 320), (129, 496), (68, 336), (35, 437), (16, 1), (10, 79)]
    (codeMat 354) (codeMat 335) (codeMat 426) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane462GenSource0106 :
    QuotientRankAtLeast (spanCodes [256, 131, 66, 49, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(256, 63), (131, 43), (66, 53), (49, 296), (10, 344), (6, 32)]
    (codeMat 141) (codeMat 375) (codeMat 491) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane462GenSource0107 :
    QuotientRankAtLeast (spanCodes [262, 130, 68, 48, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(262, 42), (130, 63), (68, 20), (48, 365), (10, 284), (1, 32)]
    (codeMat 460) (codeMat 242) (codeMat 205) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane462GenSource0108 :
    QuotientRankAtLeast (spanCodes [276, 144, 68, 34, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(276, 446), (144, 1), (68, 420), (34, 112), (10, 96), (1, 256)]
    (codeMat 86) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane462GenSource0109 :
    QuotientRankAtLeast (spanCodes [304, 178, 66, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(304, 232), (178, 245), (66, 21), (10, 149), (6, 3), (1, 2)]
    (codeMat 417) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
