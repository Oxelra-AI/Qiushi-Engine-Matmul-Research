import QiushiPlane485GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane485GenSource0200 :
    QuotientRankAtLeast (spanCodes [288, 128, 98, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(288, 27), (128, 260), (98, 94), (17, 160), (10, 176), (5, 320)]
    (codeMat 93) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane485GenSource0201 :
    QuotientRankAtLeast (spanCodes [289, 160, 66, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(289, 69), (160, 186), (66, 420), (16, 16), (10, 160), (4, 320)]
    (codeMat 87) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane485GenSource0202 :
    QuotientRankAtLeast (spanCodes [259, 160, 96, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(259, 69), (160, 170), (96, 430), (16, 16), (10, 176), (4, 320)]
    (codeMat 85) (codeMat 348) (codeMat 125) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane485GenSource0203 :
    QuotientRankAtLeast (spanCodes [256, 160, 100, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(256, 1), (160, 79), (100, 69), (20, 496), (9, 320), (3, 16)]
    (codeMat 204) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane485GenSource0204 :
    QuotientRankAtLeast (spanCodes [288, 133, 96, 20, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(288, 260), (133, 10), (96, 261), (20, 160), (8, 320), (2, 16)]
    (codeMat 140) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane485GenSource0205 :
    QuotientRankAtLeast (spanCodes [292, 164, 70, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(292, 260), (164, 276), (70, 10), (20, 436), (10, 78), (1, 1)]
    (codeMat 417) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane485GenSource0206 :
    QuotientRankAtLeast (spanCodes [288, 160, 70, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(288, 16), (160, 336), (70, 69), (20, 506), (10, 79), (1, 1)]
    (codeMat 305) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane485GenSource0207 :
    QuotientRankAtLeast (spanCodes [262, 128, 64, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(262, 139), (128, 9), (64, 1), (20, 252), (10, 31), (1, 3)]
    (codeMat 172) (codeMat 307) (codeMat 311) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane485GenSource0208 :
    QuotientRankAtLeast (spanCodes [262, 135, 65, 32, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(262, 496), (135, 160), (65, 320), (32, 1), (20, 78), (10, 437)]
    (codeMat 354) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane485GenSource0209 :
    QuotientRankAtLeast (spanCodes [262, 133, 67, 32, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(262, 496), (133, 336), (67, 480), (32, 1), (20, 79), (10, 507)]
    (codeMat 298) (codeMat 159) (codeMat 230) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
