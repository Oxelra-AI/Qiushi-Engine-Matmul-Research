import QiushiPlane468GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiWcOrbit141Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane468GenSource0110 :
    QuotientRankAtLeast (spanCodes [259, 128, 66, 36, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(259, 430), (128, 260), (66, 97), (36, 432), (22, 272), (10, 96)]
    (codeMat 142) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane468GenSource0111 :
    QuotientRankAtLeast (spanCodes [290, 164, 70, 18, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(290, 507), (164, 255), (70, 68), (18, 27), (10, 11), (1, 1)]
    (codeMat 273) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane468GenSource0112 :
    QuotientRankAtLeast (spanCodes [262, 135, 67, 35, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(262, 238), (135, 180), (67, 462), (35, 170), (23, 308), (10, 463)]
    (codeMat 415) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit76_lb15_unconditional

theorem plane468GenSource0113 :
    QuotientRankAtLeast (spanCodes [261, 134, 65, 34, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(261, 11), (134, 21), (65, 1), (34, 191), (21, 475), (10, 127)]
    (codeMat 165) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane468GenSource0114 :
    QuotientRankAtLeast (spanCodes [289, 164, 69, 17, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(289, 463), (164, 191), (69, 112), (17, 10), (8, 1), (2, 16)]
    (codeMat 266) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane468GenSource0115 :
    QuotientRankAtLeast (spanCodes [289, 164, 68, 16, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(289, 463), (164, 223), (68, 112), (16, 27), (9, 1), (3, 16)]
    (codeMat 331) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane468GenSource0116 :
    QuotientRankAtLeast (spanCodes [259, 133, 69, 33, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 126), (133, 252), (69, 245), (33, 232), (17, 104), (10, 96)]
    (codeMat 159) (codeMat 481) (codeMat 185) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane468GenSource0117 :
    QuotientRankAtLeast (spanCodes [292, 164, 67, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(292, 3), (164, 35), (67, 381), (23, 118), (10, 383)]
    (codeMat 167) (codeMat 190) (codeMat 355) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

theorem plane468GenSource0118 :
    QuotientRankAtLeast (spanCodes [256, 129, 66, 37, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(256, 260), (129, 160), (66, 272), (37, 453), (22, 170), (10, 464)]
    (codeMat 271) (codeMat 340) (codeMat 85) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane468GenSource0119 :
    QuotientRankAtLeast (spanCodes [288, 164, 70, 18, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(288, 320), (164, 245), (70, 78), (18, 27), (10, 11), (1, 1)]
    (codeMat 401) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
