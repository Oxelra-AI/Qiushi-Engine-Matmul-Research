import QiushiPlane464GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane464GenSource0070 :
    QuotientRankAtLeast (spanCodes [257, 160, 64, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(257, 69), (160, 170), (64, 260), (16, 16), (10, 160), (4, 320)]
    (codeMat 85) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane464GenSource0071 :
    QuotientRankAtLeast (spanCodes [256, 162, 65, 19, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(256, 27), (162, 197), (65, 1), (19, 446), (10, 113), (5, 16)]
    (codeMat 461) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane464GenSource0072 :
    QuotientRankAtLeast (spanCodes [257, 160, 68, 20, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(257, 69), (160, 238), (68, 68), (20, 240), (8, 288), (2, 384)]
    (codeMat 93) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit76_lb15_unconditional

theorem plane464GenSource0073 :
    QuotientRankAtLeast (spanCodes [277, 129, 68, 53, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(277, 117), (129, 283), (68, 420), (53, 453), (8, 260), (2, 192)]
    (codeMat 123) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane464GenSource0074 :
    QuotientRankAtLeast (spanCodes [278, 134, 68, 50, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(278, 363), (134, 197), (68, 452), (50, 368), (10, 352), (1, 256)]
    (codeMat 85) (codeMat 230) (codeMat 159) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane464GenSource0075 :
    QuotientRankAtLeast (spanCodes [288, 176, 64, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(288, 8), (176, 104), (64, 128), (10, 148), (4, 1), (1, 2)]
    (codeMat 305) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane464GenSource0076 :
    QuotientRankAtLeast (spanCodes [290, 178, 66, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(290, 136), (178, 104), (66, 151), (10, 148), (6, 128), (1, 2)]
    (codeMat 143) (codeMat 177) (codeMat 417) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane464GenSource0077 :
    QuotientRankAtLeast (spanCodes [275, 129, 64, 49, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(275, 117), (129, 475), (64, 192), (49, 272), (10, 420), (4, 260)]
    (codeMat 86) (codeMat 470) (codeMat 213) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane464GenSource0078 :
    QuotientRankAtLeast (spanCodes [276, 133, 68, 49, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(276, 21), (133, 127), (68, 420), (49, 261), (9, 260), (3, 192)]
    (codeMat 122) (codeMat 242) (codeMat 205) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane464GenSource0079 :
    QuotientRankAtLeast (spanCodes [288, 178, 66, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(288, 9), (178, 252), (66, 149), (10, 148), (6, 130), (1, 2)]
    (codeMat 142) (codeMat 181) (codeMat 423) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
