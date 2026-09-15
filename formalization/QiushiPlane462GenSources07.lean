import QiushiPlane462GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane462GenSource0070 :
    QuotientRankAtLeast (spanCodes [276, 128, 68, 50, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(276, 463), (128, 1), (68, 452), (50, 112), (10, 96), (1, 256)]
    (codeMat 84) (codeMat 358) (codeMat 158) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane462GenSource0071 :
    QuotientRankAtLeast (spanCodes [288, 178, 66, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(288, 9), (178, 252), (66, 149), (10, 148), (6, 130), (1, 2)]
    (codeMat 142) (codeMat 181) (codeMat 423) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane462GenSource0072 :
    QuotientRankAtLeast (spanCodes [290, 178, 64, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(290, 28), (178, 252), (64, 128), (10, 148), (4, 3), (1, 2)]
    (codeMat 305) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane462GenSource0073 :
    QuotientRankAtLeast (spanCodes [256, 130, 68, 32, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 8), (130, 128), (68, 104), (32, 1), (16, 2), (10, 148)]
    (codeMat 354) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane462GenSource0074 :
    QuotientRankAtLeast (spanCodes [258, 128, 68, 34, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 31), (128, 3), (68, 252), (34, 22), (16, 2), (10, 148)]
    (codeMat 86) (codeMat 110) (codeMat 444) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane462GenSource0075 :
    QuotientRankAtLeast (spanCodes [261, 135, 68, 37, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(261, 363), (135, 436), (68, 437), (37, 368), (16, 256), (10, 96)]
    (codeMat 157) (codeMat 229) (codeMat 187) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane462GenSource0076 :
    QuotientRankAtLeast (spanCodes [260, 134, 68, 37, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 16), (134, 160), (68, 336), (37, 506), (17, 78), (10, 79)]
    (codeMat 299) (codeMat 249) (codeMat 425) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane462GenSource0077 :
    QuotientRankAtLeast (spanCodes [257, 130, 68, 32, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 96), (130, 1), (68, 104), (32, 128), (16, 2), (10, 148)]
    (codeMat 85) (codeMat 330) (codeMat 394) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane462GenSource0078 :
    QuotientRankAtLeast (spanCodes [259, 128, 68, 34, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 104), (128, 128), (68, 224), (34, 148), (16, 2), (10, 151)]
    (codeMat 298) (codeMat 345) (codeMat 345) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane462GenSource0079 :
    QuotientRankAtLeast (spanCodes [261, 134, 68, 36, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(261, 378), (134, 180), (68, 469), (36, 16), (16, 256), (10, 96)]
    (codeMat 158) (codeMat 225) (codeMat 169) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

end QiushiMatmul
