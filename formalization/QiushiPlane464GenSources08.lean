import QiushiPlane464GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit69Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiWcOrbit72Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane464GenSource0080 :
    QuotientRankAtLeast (spanCodes [290, 176, 64, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(290, 30), (176, 232), (64, 128), (10, 150), (4, 3), (1, 2)]
    (codeMat 305) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane464GenSource0081 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 32, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (132, 20), (68, 148), (32, 1), (16, 8), (10, 104)]
    (codeMat 98) (codeMat 92) (codeMat 116) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane464GenSource0082 :
    QuotientRankAtLeast (spanCodes [262, 130, 68, 33, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(262, 222), (130, 432), (68, 367), (33, 191), (23, 127), (10, 420)]
    (codeMat 244) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane464GenSource0083 :
    QuotientRankAtLeast (spanCodes [258, 135, 68, 39, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(258, 326), (135, 259), (68, 258), (39, 112), (20, 344), (10, 80)]
    (codeMat 93) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane464GenSource0084 :
    QuotientRankAtLeast (spanCodes [260, 129, 68, 35, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(260, 260), (129, 378), (68, 180), (35, 283), (22, 356), (10, 191)]
    (codeMat 254) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane464GenSource0085 :
    QuotientRankAtLeast (spanCodes [258, 135, 68, 37, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(258, 238), (135, 90), (68, 378), (37, 170), (22, 414), (10, 251)]
    (codeMat 470) (codeMat 351) (codeMat 239) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit76_lb15_unconditional

theorem plane464GenSource0086 :
    QuotientRankAtLeast (spanCodes [278, 146, 68, 38, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(278, 446), (146, 1), (68, 420), (38, 112), (10, 352), (1, 256)]
    (codeMat 95) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane464GenSource0087 :
    QuotientRankAtLeast (spanCodes [257, 135, 68, 34, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 150), (135, 149), (68, 148), (34, 232), (17, 96), (10, 104)]
    (codeMat 157) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane464GenSource0088 :
    QuotientRankAtLeast (spanCodes [276, 145, 68, 37, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(276, 433), (145, 261), (68, 420), (37, 475), (9, 192), (3, 260)]
    (codeMat 103) (codeMat 358) (codeMat 158) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane464GenSource0089 :
    QuotientRankAtLeast (spanCodes [261, 130, 68, 37, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(261, 437), (130, 1), (68, 363), (37, 430), (19, 446), (10, 463)]
    (codeMat 477) (codeMat 110) (codeMat 444) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

end QiushiMatmul
