import QiushiPlane476GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiStep81Qdim2Generated
import QiushiStep99Orbit56Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit78Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane476GenSource0070 :
    QuotientRankAtLeast (spanCodes [275, 128, 80, 48, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(275, 181), (128, 192), (80, 283), (48, 260), (10, 420), (7, 432)]
    (codeMat 159) (codeMat 141) (codeMat 226) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane476GenSource0071 :
    QuotientRankAtLeast (spanCodes [259, 160, 96, 16, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(259, 11), (160, 196), (96, 197), (16, 256), (10, 352), (7, 16)]
    (codeMat 140) (codeMat 229) (codeMat 187) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane476GenSource0072 :
    QuotientRankAtLeast (spanCodes [276, 132, 81, 49, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(276, 463), (132, 97), (81, 462), (49, 272), (8, 432), (2, 260)]
    (codeMat 93) (codeMat 494) (codeMat 501) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane476GenSource0073 :
    QuotientRankAtLeast (spanCodes [275, 144, 80, 48, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(275, 275), (144, 1), (80, 129), (48, 390), (10, 138), (7, 365)]
    (codeMat 286) (codeMat 303) (codeMat 286) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane476GenSource0074 :
    QuotientRankAtLeast (spanCodes [259, 129, 64, 32, 17, 10, 6]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(259, 100), (129, 374), (64, 219), (32, 32), (17, 240), (10, 408), (6, 128)]
    (codeMat 87) (codeMat 409) (codeMat 473) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane476GenSource0075 :
    QuotientRankAtLeast (spanCodes [262, 133, 64, 32, 18, 10]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 80, 12, 2, 1] [(262, 268), (133, 162), (64, 511), (32, 1), (18, 256), (10, 259)]
    (codeMat 234) (codeMat 205) (codeMat 242) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit56_lb14_unconditional

theorem plane476GenSource0076 :
    QuotientRankAtLeast (spanCodes [257, 132, 68, 36, 21, 8, 2]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(257, 69), (132, 450), (68, 68), (36, 360), (21, 80), (8, 32), (2, 128)]
    (codeMat 85) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane476GenSource0077 :
    QuotientRankAtLeast (spanCodes [260, 132, 96, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 432), (132, 176), (96, 70), (16, 2), (8, 1), (2, 16), (1, 8)]
    (codeMat 266) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane476GenSource0078 :
    QuotientRankAtLeast (spanCodes [274, 128, 66, 34, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(274, 238), (128, 325), (66, 170), (34, 424), (10, 168), (6, 24), (1, 16)]
    (codeMat 142) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane476GenSource0079 :
    QuotientRankAtLeast (spanCodes [273, 145, 81, 49, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(273, 501), (145, 503), (81, 502), (49, 176), (9, 432), (5, 24), (3, 8)]
    (codeMat 140) (codeMat 478) (codeMat 445) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
