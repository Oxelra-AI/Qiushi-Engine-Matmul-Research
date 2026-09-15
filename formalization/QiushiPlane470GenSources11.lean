import QiushiPlane470GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiStep99Orbit77Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane470GenSource0110 :
    QuotientRankAtLeast (spanCodes [259, 131, 67, 33, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 104), (131, 105), (67, 97), (33, 252), (23, 255), (10, 227)]
    (codeMat 124) (codeMat 499) (codeMat 382) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane470GenSource0111 :
    QuotientRankAtLeast (spanCodes [259, 131, 69, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 224), (131, 227), (69, 255), (39, 96), (17, 97), (10, 105)]
    (codeMat 123) (codeMat 459) (codeMat 346) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane470GenSource0112 :
    QuotientRankAtLeast (spanCodes [259, 133, 69, 33, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 126), (133, 252), (69, 245), (33, 232), (17, 104), (10, 96)]
    (codeMat 159) (codeMat 481) (codeMat 185) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane470GenSource0113 :
    QuotientRankAtLeast (spanCodes [259, 147, 80, 34, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(259, 26), (147, 446), (80, 447), (34, 176), (10, 496), (4, 16)]
    (codeMat 141) (codeMat 249) (codeMat 425) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane470GenSource0114 :
    QuotientRankAtLeast (spanCodes [258, 166, 70, 18, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 480), (166, 255), (70, 176), (18, 27), (10, 26), (1, 16)]
    (codeMat 330) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane470GenSource0115 :
    QuotientRankAtLeast (spanCodes [259, 135, 67, 38, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(259, 475), (135, 452), (67, 223), (38, 21), (23, 453), (10, 367)]
    (codeMat 286) (codeMat 110) (codeMat 444) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane470GenSource0116 :
    QuotientRankAtLeast (spanCodes [259, 130, 67, 35, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(259, 20), (130, 432), (67, 272), (35, 21), (23, 378), (10, 464)]
    (codeMat 270) (codeMat 212) (codeMat 86) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane470GenSource0117 :
    QuotientRankAtLeast (spanCodes [259, 129, 67, 32, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 128, 96, 20, 10, 1] [(259, 378), (129, 149), (67, 506), (32, 260), (23, 283), (10, 507)]
    (codeMat 167) (codeMat 407) (codeMat 405) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit77_lb15_unconditional

theorem plane470GenSource0118 :
    QuotientRankAtLeast (spanCodes [259, 135, 70, 35, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(259, 20), (135, 11), (70, 21), (35, 272), (18, 192), (10, 368)]
    (codeMat 205) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane470GenSource0119 :
    QuotientRankAtLeast (spanCodes [257, 165, 69, 17, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(257, 463), (165, 181), (69, 113), (17, 10), (8, 1), (2, 16)]
    (codeMat 394) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

end QiushiMatmul
