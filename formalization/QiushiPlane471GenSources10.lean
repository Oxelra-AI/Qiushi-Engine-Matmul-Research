import QiushiPlane471GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit197Dispatch
import QiushiWcOrbit233Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane471GenSource0100 :
    QuotientRankAtLeast (spanCodes [273, 145, 84, 48, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(273, 410), (145, 411), (84, 442), (48, 2), (10, 493)]
    (codeMat 340) (codeMat 498) (codeMat 206) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane471GenSource0101 :
    QuotientRankAtLeast (spanCodes [289, 161, 84, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 140, 98, 16, 1] [(289, 392), (161, 140), (84, 115), (8, 1), (2, 16)]
    (codeMat 394) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit233_lb15_wc

theorem plane471GenSource0102 :
    QuotientRankAtLeast (spanCodes [274, 144, 83, 51, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(274, 97), (144, 1), (83, 433), (51, 420), (10, 127), (7, 192)]
    (codeMat 102) (codeMat 335) (codeMat 426) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane471GenSource0103 :
    QuotientRankAtLeast (spanCodes [256, 130, 82, 33, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(256, 1), (130, 27), (82, 197), (33, 96), (10, 368), (6, 16)]
    (codeMat 204) (codeMat 87) (codeMat 468) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane471GenSource0104 :
    QuotientRankAtLeast (spanCodes [274, 144, 82, 51, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(274, 223), (144, 1), (82, 31), (51, 160), (10, 20), (6, 432)]
    (codeMat 214) (codeMat 303) (codeMat 286) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane471GenSource0105 :
    QuotientRankAtLeast (spanCodes [259, 131, 83, 34, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(259, 452), (131, 453), (83, 170), (34, 96), (10, 464), (7, 192)]
    (codeMat 92) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane471GenSource0106 :
    QuotientRankAtLeast (spanCodes [258, 128, 80, 35, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 10), (128, 1), (80, 79), (35, 160), (10, 496), (4, 16)]
    (codeMat 204) (codeMat 107) (codeMat 428) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane471GenSource0107 :
    QuotientRankAtLeast (spanCodes [273, 128, 84, 48, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(273, 174), (128, 32), (84, 491), (48, 448), (10, 164)]
    (codeMat 167) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane471GenSource0108 :
    QuotientRankAtLeast (spanCodes [261, 133, 69, 36, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(261, 96), (133, 105), (69, 104), (36, 128), (17, 150), (10, 148)]
    (codeMat 92) (codeMat 474) (codeMat 395) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane471GenSource0109 :
    QuotientRankAtLeast (spanCodes [262, 134, 69, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(262, 104), (134, 96), (69, 224), (39, 148), (17, 149), (10, 151)]
    (codeMat 355) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
