import QiushiPlane472GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit192From65
import QiushiMonoOrbit198From77T
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane472GenSource0100 :
    QuotientRankAtLeast (spanCodes [259, 130, 66, 33, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(259, 97), (130, 1), (66, 261), (33, 191), (22, 367), (10, 453)]
    (codeMat 285) (codeMat 358) (codeMat 158) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane472GenSource0101 :
    QuotientRankAtLeast (spanCodes [256, 129, 66, 34, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(256, 1), (129, 196), (66, 452), (34, 463), (22, 446), (10, 479)]
    (codeMat 340) (codeMat 159) (codeMat 230) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane472GenSource0102 :
    QuotientRankAtLeast (spanCodes [259, 133, 69, 33, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 126), (133, 252), (69, 245), (33, 232), (17, 104), (10, 96)]
    (codeMat 159) (codeMat 481) (codeMat 185) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane472GenSource0103 :
    QuotientRankAtLeast (spanCodes [257, 132, 70, 35, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(257, 170), (132, 251), (70, 414), (35, 78), (18, 288), (10, 289)]
    (codeMat 426) (codeMat 485) (codeMat 171) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit76_lb15_unconditional

theorem plane472GenSource0104 :
    QuotientRankAtLeast (spanCodes [259, 144, 80, 33, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(259, 69), (144, 16), (80, 336), (33, 79), (10, 506), (4, 1)]
    (codeMat 305) (codeMat 93) (codeMat 372) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane472GenSource0105 :
    QuotientRankAtLeast (spanCodes [259, 147, 83, 33, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(259, 17), (147, 368), (83, 363), (33, 113), (10, 430), (7, 16)]
    (codeMat 461) (codeMat 206) (codeMat 498) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane472GenSource0106 :
    QuotientRankAtLeast (spanCodes [274, 134, 84, 48, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 132, 32, 10, 1] [(274, 133), (134, 326), (84, 174), (48, 1), (10, 456)]
    (codeMat 442) (codeMat 460) (codeMat 122) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit198_lb15_mono

theorem plane472GenSource0107 :
    QuotientRankAtLeast (spanCodes [257, 130, 67, 35, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(257, 452), (130, 1), (67, 69), (35, 414), (23, 463), (10, 357)]
    (codeMat 285) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit76_lb15_unconditional

theorem plane472GenSource0108 :
    QuotientRankAtLeast (spanCodes [290, 164, 70, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 128, 32, 10, 1] [(290, 469), (164, 341), (70, 160), (18, 511), (10, 510)]
    (codeMat 354) (codeMat 478) (codeMat 445) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit192_lb15_mono

theorem plane472GenSource0109 :
    QuotientRankAtLeast (spanCodes [261, 128, 69, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(261, 148), (128, 130), (69, 150), (39, 104), (17, 97), (10, 105)]
    (codeMat 99) (codeMat 491) (codeMat 375) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
