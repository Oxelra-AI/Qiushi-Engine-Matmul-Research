import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit187Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0280 :
    QuotientRankAtLeast (spanCodes [275, 130, 83, 51, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(275, 244), (130, 27), (83, 228), (51, 436), (10, 507), (7, 1)]
    (codeMat 417) (codeMat 351) (codeMat 239) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane490GenSource0281 :
    QuotientRankAtLeast (spanCodes [274, 162, 66, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(274, 246), (162, 255), (66, 151), (10, 150), (4, 128), (1, 2)]
    (codeMat 142) (codeMat 403) (codeMat 403) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0282 :
    QuotientRankAtLeast (spanCodes [274, 162, 64, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(274, 127), (162, 119), (64, 128), (10, 151), (6, 1), (1, 2)]
    (codeMat 305) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0283 :
    QuotientRankAtLeast (spanCodes [275, 145, 67, 51, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(275, 99), (145, 139), (67, 245), (51, 227), (10, 252), (7, 3)]
    (codeMat 183) (codeMat 409) (codeMat 473) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0284 :
    QuotientRankAtLeast (spanCodes [275, 147, 67, 49, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(275, 156), (147, 30), (67, 235), (49, 136), (10, 232), (7, 8)]
    (codeMat 207) (codeMat 409) (codeMat 473) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0285 :
    QuotientRankAtLeast (spanCodes [275, 129, 83, 48, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(275, 85), (129, 447), (83, 78), (48, 16), (10, 496), (4, 320)]
    (codeMat 86) (codeMat 478) (codeMat 445) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane490GenSource0286 :
    QuotientRankAtLeast (spanCodes [275, 147, 80, 32, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(275, 421), (147, 446), (80, 447), (32, 320), (10, 496), (5, 16)]
    (codeMat 141) (codeMat 477) (codeMat 431) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane490GenSource0287 :
    QuotientRankAtLeast (spanCodes [275, 144, 82, 33, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(275, 277), (144, 1), (82, 447), (33, 336), (10, 496), (5, 16)]
    (codeMat 206) (codeMat 335) (codeMat 426) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane490GenSource0288 :
    QuotientRankAtLeast (spanCodes [275, 144, 65, 54, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(275, 171), (144, 390), (65, 128), (54, 1), (10, 294)]
    (codeMat 379) (codeMat 444) (codeMat 110) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane490GenSource0289 :
    QuotientRankAtLeast (spanCodes [275, 130, 83, 49, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(275, 254), (130, 27), (83, 255), (49, 336), (10, 480), (7, 16)]
    (codeMat 204) (codeMat 379) (codeMat 247) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
