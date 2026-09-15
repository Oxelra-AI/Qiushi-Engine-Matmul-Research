import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiOrbit31FP
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit69Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource0380 :
    QuotientRankAtLeast (spanCodes [289, 161, 65, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(289, 352), (161, 379), (65, 1), (19, 446), (10, 113), (7, 16)]
    (codeMat 461) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane484GenSource0381 :
    QuotientRankAtLeast (spanCodes [289, 161, 66, 19, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(289, 10), (161, 266), (66, 112), (19, 446), (10, 113), (4, 16)]
    (codeMat 270) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane484GenSource0382 :
    QuotientRankAtLeast (spanCodes [290, 131, 99, 19, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(290, 10), (131, 112), (99, 282), (19, 113), (10, 446), (4, 16)]
    (codeMat 334) (codeMat 106) (codeMat 396) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane484GenSource0383 :
    QuotientRankAtLeast (spanCodes [288, 160, 67, 19, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(288, 27), (160, 283), (67, 112), (19, 463), (10, 113), (5, 16)]
    (codeMat 271) (codeMat 183) (codeMat 419) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane484GenSource0384 :
    QuotientRankAtLeast (spanCodes [257, 162, 96, 19, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(257, 272), (162, 196), (96, 180), (19, 463), (10, 446), (5, 16)]
    (codeMat 335) (codeMat 474) (codeMat 395) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane484GenSource0385 :
    QuotientRankAtLeast (spanCodes [261, 128, 65, 17, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(261, 68), (128, 40), (65, 1), (17, 20), (8, 2), (2, 32)]
    (codeMat 85) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane484GenSource0386 :
    QuotientRankAtLeast (spanCodes [261, 129, 65, 16, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(261, 100), (129, 33), (65, 9), (16, 2), (9, 54), (3, 32)]
    (codeMat 85) (codeMat 267) (codeMat 282) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane484GenSource0387 :
    QuotientRankAtLeast (spanCodes [260, 132, 71, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(260, 2), (132, 34), (71, 35), (19, 441), (10, 462)]
    (codeMat 421) (codeMat 249) (codeMat 425) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0388 :
    QuotientRankAtLeast (spanCodes [258, 130, 71, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(258, 33), (130, 1), (71, 34), (19, 119), (10, 441)]
    (codeMat 421) (codeMat 334) (codeMat 442) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0389 :
    QuotientRankAtLeast (spanCodes [256, 128, 71, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(256, 2), (128, 1), (71, 35), (19, 119), (10, 462)]
    (codeMat 428) (codeMat 107) (codeMat 428) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

end QiushiMatmul
