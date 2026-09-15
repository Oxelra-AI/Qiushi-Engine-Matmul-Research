import QiushiPlane471GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit112From35T
import QiushiMonoOrbit149From65
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit187Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit236Dispatch
import QiushiWcOrbit238Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane471GenSource0070 :
    QuotientRankAtLeast (spanCodes [275, 133, 84, 50, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(275, 285), (133, 310), (84, 143), (50, 408), (10, 440)]
    (codeMat 87) (codeMat 477) (codeMat 431) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane471GenSource0071 :
    QuotientRankAtLeast (spanCodes [262, 144, 84, 39, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(262, 373), (144, 32), (84, 382), (39, 497), (10, 496)]
    (codeMat 443) (codeMat 340) (codeMat 85) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane471GenSource0072 :
    QuotientRankAtLeast (spanCodes [260, 146, 84, 37, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(260, 256), (146, 1), (84, 286), (37, 383), (10, 362)]
    (codeMat 351) (codeMat 331) (codeMat 410) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane471GenSource0073 :
    QuotientRankAtLeast (spanCodes [258, 148, 84, 35, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(258, 462), (148, 252), (84, 253), (35, 21), (10, 327)]
    (codeMat 468) (codeMat 230) (codeMat 159) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane471GenSource0074 :
    QuotientRankAtLeast (spanCodes [256, 150, 84, 33, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(256, 1), (150, 97), (84, 358), (33, 399), (10, 252)]
    (codeMat 380) (codeMat 205) (codeMat 242) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane471GenSource0075 :
    QuotientRankAtLeast (spanCodes [289, 161, 66, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(289, 11), (161, 499), (66, 133), (22, 278), (10, 132)]
    (codeMat 206) (codeMat 167) (codeMat 167) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane471GenSource0076 :
    QuotientRankAtLeast (spanCodes [288, 70, 18, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 68, 16, 10, 1] [(288, 16), (70, 79), (18, 325), (10, 69), (1, 1)]
    (codeMat 177) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit149_lb15_mono

theorem plane471GenSource0077 :
    QuotientRankAtLeast (spanCodes [289, 64, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(289, 422), (64, 128), (17, 11), (10, 10), (5, 32)]
    (codeMat 267) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane471GenSource0078 :
    QuotientRankAtLeast (spanCodes [289, 67, 17, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(289, 129), (67, 269), (17, 300), (10, 268), (6, 390)]
    (codeMat 415) (codeMat 167) (codeMat 167) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane471GenSource0079 :
    QuotientRankAtLeast (spanCodes [288, 66, 22, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 8, 2, 1] [(288, 2), (66, 105), (22, 376), (10, 104), (1, 8)]
    (codeMat 142) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit112_lb15_mono

end QiushiMatmul
