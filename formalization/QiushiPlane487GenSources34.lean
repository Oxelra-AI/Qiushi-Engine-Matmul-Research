import QiushiPlane487GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep128Mono189From80T
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit197Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane487GenSource0340 :
    QuotientRankAtLeast (spanCodes [260, 134, 65, 36, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(260, 2), (134, 148), (65, 128), (36, 3), (21, 252), (10, 224)]
    (codeMat 110) (codeMat 212) (codeMat 86) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane487GenSource0341 :
    QuotientRankAtLeast (spanCodes [258, 133, 64, 32, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 496), (133, 160), (64, 320), (32, 1), (20, 78), (10, 437)]
    (codeMat 298) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane487GenSource0342 :
    QuotientRankAtLeast (spanCodes [289, 132, 64, 20, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(289, 20), (132, 97), (64, 130), (20, 96), (8, 128), (2, 8)]
    (codeMat 142) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane487GenSource0343 :
    QuotientRankAtLeast (spanCodes [288, 132, 66, 22, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(288, 128), (132, 246), (66, 29), (22, 255), (10, 31), (1, 3)]
    (codeMat 183) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane487GenSource0344 :
    QuotientRankAtLeast (spanCodes [276, 146, 84, 50, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(276, 133), (146, 325), (84, 165), (50, 367), (10, 366)]
    (codeMat 354) (codeMat 234) (codeMat 461) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane487GenSource0345 :
    QuotientRankAtLeast (spanCodes [288, 129, 65, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(288, 32), (129, 129), (65, 1), (21, 413), (10, 139)]
    (codeMat 309) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane487GenSource0346 :
    QuotientRankAtLeast (spanCodes [261, 128, 65, 36, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(261, 366), (128, 1), (65, 432), (36, 192), (21, 356), (10, 127)]
    (codeMat 244) (codeMat 110) (codeMat 444) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane487GenSource0347 :
    QuotientRankAtLeast (spanCodes [260, 135, 65, 34, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(260, 128), (135, 20), (65, 130), (34, 224), (21, 28), (10, 227)]
    (codeMat 111) (codeMat 337) (codeMat 337) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane487GenSource0348 :
    QuotientRankAtLeast (spanCodes [256, 134, 67, 37, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(256, 320), (134, 336), (67, 480), (37, 437), (23, 79), (10, 507)]
    (codeMat 298) (codeMat 415) (codeMat 253) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane487GenSource0349 :
    QuotientRankAtLeast (spanCodes [261, 131, 67, 37, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(261, 480), (131, 160), (67, 176), (37, 507), (23, 78), (10, 436)]
    (codeMat 354) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
