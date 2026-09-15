import QiushiPlane487GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit112From35T
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit187Dispatch
import QiushiWcOrbit197Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane487GenSource0280 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 128), (130, 8), (64, 2), (20, 224), (10, 28), (1, 3)]
    (codeMat 165) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane487GenSource0281 :
    QuotientRankAtLeast (spanCodes [292, 160, 70, 18, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(292, 27), (160, 480), (70, 79), (18, 260), (10, 68), (1, 1)]
    (codeMat 177) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane487GenSource0282 :
    QuotientRankAtLeast (spanCodes [274, 148, 84, 39, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(274, 132), (148, 164), (84, 481), (39, 367), (10, 366)]
    (codeMat 491) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane487GenSource0283 :
    QuotientRankAtLeast (spanCodes [262, 146, 84, 53, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 8, 2, 1] [(262, 371), (146, 9), (84, 377), (53, 272), (10, 274)]
    (codeMat 159) (codeMat 351) (codeMat 239) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit112_lb15_mono

theorem plane487GenSource0284 :
    QuotientRankAtLeast (spanCodes [274, 148, 84, 36, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(274, 11), (148, 139), (84, 171), (36, 1), (10, 295)]
    (codeMat 355) (codeMat 95) (codeMat 244) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane487GenSource0285 :
    QuotientRankAtLeast (spanCodes [273, 134, 84, 53, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(273, 335), (134, 164), (84, 143), (53, 367), (10, 366)]
    (codeMat 379) (codeMat 409) (codeMat 473) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane487GenSource0286 :
    QuotientRankAtLeast (spanCodes [260, 144, 84, 48, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(260, 32), (144, 325), (84, 165), (48, 1), (10, 366)]
    (codeMat 298) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane487GenSource0287 :
    QuotientRankAtLeast (spanCodes [259, 147, 80, 48, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(259, 261), (147, 447), (80, 446), (48, 16), (10, 496), (4, 320)]
    (codeMat 85) (codeMat 478) (codeMat 445) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane487GenSource0288 :
    QuotientRankAtLeast (spanCodes [273, 130, 81, 50, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(273, 158), (130, 3), (81, 28), (50, 232), (10, 224), (5, 128)]
    (codeMat 85) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane487GenSource0289 :
    QuotientRankAtLeast (spanCodes [274, 146, 83, 35, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(274, 26), (146, 1), (83, 446), (35, 336), (10, 496), (7, 320)]
    (codeMat 95) (codeMat 106) (codeMat 396) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
