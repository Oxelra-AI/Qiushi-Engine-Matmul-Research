import QiushiPlane474GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiWcOrbit183Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane474GenSource0060 :
    QuotientRankAtLeast (spanCodes [274, 146, 81, 49, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(274, 257), (146, 256), (81, 283), (49, 113), (10, 479), (5, 16)]
    (codeMat 460) (codeMat 461) (codeMat 234) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane474GenSource0061 :
    QuotientRankAtLeast (spanCodes [292, 164, 84, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(292, 511), (164, 510), (84, 500), (8, 32), (2, 384)]
    (codeMat 84) (codeMat 500) (codeMat 94) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane474GenSource0062 :
    QuotientRankAtLeast (spanCodes [258, 131, 83, 35, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(258, 78), (131, 367), (83, 453), (35, 160), (10, 464), (7, 288)]
    (codeMat 213) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit76_lb15_unconditional

theorem plane474GenSource0063 :
    QuotientRankAtLeast (spanCodes [260, 135, 65, 34, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(260, 128), (135, 20), (65, 130), (34, 224), (21, 28), (10, 227)]
    (codeMat 111) (codeMat 337) (codeMat 337) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane474GenSource0064 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 38, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 9), (128, 8), (66, 96), (38, 31), (22, 28), (10, 224)]
    (codeMat 116) (codeMat 116) (codeMat 92) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane474GenSource0065 :
    QuotientRankAtLeast (spanCodes [292, 161, 69, 17, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(292, 27), (161, 491), (69, 480), (17, 69), (8, 260), (2, 320)]
    (codeMat 99) (codeMat 230) (codeMat 159) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane474GenSource0066 :
    QuotientRankAtLeast (spanCodes [261, 129, 69, 35, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(261, 79), (129, 436), (69, 78), (35, 336), (17, 176), (10, 160)]
    (codeMat 156) (codeMat 492) (codeMat 115) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane474GenSource0067 :
    QuotientRankAtLeast (spanCodes [260, 128, 69, 34, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 27), (128, 260), (69, 238), (34, 480), (17, 176), (10, 160)]
    (codeMat 158) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane474GenSource0068 :
    QuotientRankAtLeast (spanCodes [294, 160, 70, 18, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(294, 507), (160, 480), (70, 11), (18, 260), (10, 68), (1, 1)]
    (codeMat 161) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane474GenSource0069 :
    QuotientRankAtLeast (spanCodes [294, 162, 68, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(294, 446), (162, 78), (68, 176), (16, 1), (10, 10), (1, 16)]
    (codeMat 266) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
