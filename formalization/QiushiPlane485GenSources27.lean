import QiushiPlane485GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit65Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane485GenSource0270 :
    QuotientRankAtLeast (spanCodes [320, 161, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(320, 32), (161, 492), (19, 119), (10, 441), (7, 1)]
    (codeMat 305) (codeMat 346) (codeMat 459) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane485GenSource0271 :
    QuotientRankAtLeast (spanCodes [291, 162, 99, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(291, 261), (162, 186), (99, 286), (16, 16), (10, 176), (4, 320)]
    (codeMat 86) (codeMat 348) (codeMat 125) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane485GenSource0272 :
    QuotientRankAtLeast (spanCodes [257, 162, 65, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(257, 261), (162, 170), (65, 260), (16, 16), (10, 160), (4, 320)]
    (codeMat 84) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane485GenSource0273 :
    QuotientRankAtLeast (spanCodes [257, 162, 64, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(257, 321), (162, 78), (64, 260), (17, 176), (10, 160), (5, 320)]
    (codeMat 93) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane485GenSource0274 :
    QuotientRankAtLeast (spanCodes [260, 129, 97, 20, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 260), (129, 186), (97, 69), (20, 160), (8, 320), (2, 16)]
    (codeMat 143) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane485GenSource0275 :
    QuotientRankAtLeast (spanCodes [292, 165, 100, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(292, 1), (165, 431), (100, 261), (20, 496), (9, 320), (3, 16)]
    (codeMat 207) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane485GenSource0276 :
    QuotientRankAtLeast (spanCodes [261, 128, 69, 39, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(261, 148), (128, 128), (69, 150), (39, 252), (20, 224), (10, 255)]
    (codeMat 103) (codeMat 489) (codeMat 241) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane485GenSource0277 :
    QuotientRankAtLeast (spanCodes [263, 134, 65, 39, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(263, 176), (134, 480), (65, 320), (39, 436), (20, 507), (10, 437)]
    (codeMat 355) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane485GenSource0278 :
    QuotientRankAtLeast (spanCodes [260, 130, 69, 36, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(260, 2), (130, 3), (69, 150), (36, 128), (20, 136), (10, 232)]
    (codeMat 213) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane485GenSource0279 :
    QuotientRankAtLeast (spanCodes [260, 134, 69, 32, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(260, 2), (134, 22), (69, 148), (32, 3), (20, 31), (10, 252)]
    (codeMat 111) (codeMat 94) (codeMat 500) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
