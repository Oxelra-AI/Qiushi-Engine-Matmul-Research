import QiushiPlane471GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit134From35T
import QiushiOrbit35FP
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane471GenSource0110 :
    QuotientRankAtLeast (spanCodes [258, 135, 65, 35, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(258, 180), (135, 353), (65, 27), (35, 113), (21, 97), (10, 479)]
    (codeMat 478) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane471GenSource0111 :
    QuotientRankAtLeast (spanCodes [261, 128, 65, 36, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(261, 366), (128, 1), (65, 432), (36, 192), (21, 356), (10, 127)]
    (codeMat 244) (codeMat 110) (codeMat 444) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane471GenSource0112 :
    QuotientRankAtLeast (spanCodes [261, 129, 64, 36, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(261, 193), (129, 11), (64, 1), (36, 260), (20, 180), (10, 20)]
    (codeMat 204) (codeMat 279) (codeMat 279) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane471GenSource0113 :
    QuotientRankAtLeast (spanCodes [288, 160, 68, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(288, 260), (160, 68), (68, 160), (16, 1), (10, 10), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane471GenSource0114 :
    QuotientRankAtLeast (spanCodes [288, 162, 70, 18, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(288, 16), (162, 420), (70, 78), (18, 260), (10, 68), (1, 1)]
    (codeMat 177) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane471GenSource0115 :
    QuotientRankAtLeast (spanCodes [273, 130, 84, 48, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [156, 80, 32, 2, 1] [(273, 205), (130, 1), (84, 206), (48, 32), (10, 112)]
    (codeMat 85) (codeMat 334) (codeMat 442) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit134_lb15_mono

theorem plane471GenSource0116 :
    QuotientRankAtLeast (spanCodes [276, 135, 84, 53, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(276, 119), (135, 33), (84, 87), (53, 495), (10, 493)]
    (codeMat 285) (codeMat 370) (codeMat 207) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane471GenSource0117 :
    QuotientRankAtLeast (spanCodes [260, 151, 84, 37, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(260, 3), (151, 440), (84, 442), (37, 411), (10, 493)]
    (codeMat 125) (codeMat 247) (codeMat 379) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane471GenSource0118 :
    QuotientRankAtLeast (spanCodes [259, 128, 68, 34, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 104), (128, 128), (68, 224), (34, 148), (16, 2), (10, 151)]
    (codeMat 298) (codeMat 345) (codeMat 345) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane471GenSource0119 :
    QuotientRankAtLeast (spanCodes [257, 130, 68, 32, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 96), (130, 1), (68, 104), (32, 128), (16, 2), (10, 148)]
    (codeMat 85) (codeMat 330) (codeMat 394) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
