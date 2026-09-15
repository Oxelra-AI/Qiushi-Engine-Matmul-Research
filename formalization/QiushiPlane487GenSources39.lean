import QiushiPlane487GenData
import QiushiCertifiedTransport
import QiushiOrbit29FP
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane487GenSource0390 :
    QuotientRankAtLeast (spanCodes [256, 144, 82, 32, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 9), (144, 3), (82, 252), (32, 8), (10, 224), (6, 128)]
    (codeMat 86) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane487GenSource0391 :
    QuotientRankAtLeast (spanCodes [274, 131, 82, 33, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(274, 20), (131, 246), (82, 29), (33, 96), (10, 232), (6, 128)]
    (codeMat 95) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane487GenSource0392 :
    QuotientRankAtLeast (spanCodes [258, 162, 66, 17, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 447), (162, 78), (66, 420), (17, 176), (10, 160), (7, 320)]
    (codeMat 95) (codeMat 500) (codeMat 94) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane487GenSource0393 :
    QuotientRankAtLeast (spanCodes [257, 162, 65, 17, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(257, 261), (162, 238), (65, 260), (17, 176), (10, 160), (4, 320)]
    (codeMat 92) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane487GenSource0394 :
    QuotientRankAtLeast (spanCodes [273, 145, 81, 51, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(273, 254), (145, 255), (81, 252), (51, 136), (10, 224), (5, 128)]
    (codeMat 92) (codeMat 498) (codeMat 206) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane487GenSource0395 :
    QuotientRankAtLeast (spanCodes [272, 130, 81, 33, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(272, 453), (130, 1), (81, 11), (33, 180), (10, 20), (5, 432)]
    (codeMat 213) (codeMat 271) (codeMat 314) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane487GenSource0396 :
    QuotientRankAtLeast (spanCodes [256, 135, 67, 39, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(256, 1), (135, 436), (67, 507), (39, 496), (23, 176), (10, 480)]
    (codeMat 156) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane487GenSource0397 :
    QuotientRankAtLeast (spanCodes [262, 134, 65, 34, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(262, 176), (134, 160), (65, 320), (34, 436), (21, 78), (10, 437)]
    (codeMat 354) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane487GenSource0398 :
    QuotientRankAtLeast (spanCodes [263, 134, 69, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(263, 31), (134, 252), (69, 255), (39, 22), (17, 148), (10, 150)]
    (codeMat 94) (codeMat 253) (codeMat 415) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane487GenSource0399 :
    QuotientRankAtLeast (spanCodes [260, 134, 69, 36, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(260, 1), (134, 68), (69, 70), (36, 8), (17, 160), (10, 176)]
    (codeMat 93) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

end QiushiMatmul
