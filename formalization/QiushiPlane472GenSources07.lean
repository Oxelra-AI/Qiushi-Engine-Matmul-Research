import QiushiPlane472GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit69Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiWcOrbit128Dispatch
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit220Dispatch
import QiushiWcOrbit72Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane472GenSource0070 :
    QuotientRankAtLeast (spanCodes [259, 65, 33, 16, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(259, 81), (65, 365), (33, 33), (16, 63), (10, 21), (5, 32)]
    (codeMat 459) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane472GenSource0071 :
    QuotientRankAtLeast (spanCodes [277, 84, 53, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(277, 94), (84, 116), (53, 126), (8, 1), (2, 511)]
    (codeMat 426) (codeMat 179) (codeMat 421) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane472GenSource0072 :
    QuotientRankAtLeast (spanCodes [288, 129, 84, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(288, 384), (129, 10), (84, 84), (8, 32), (2, 1)]
    (codeMat 161) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane472GenSource0073 :
    QuotientRankAtLeast (spanCodes [290, 130, 82, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(290, 17), (130, 192), (82, 363), (10, 414), (6, 16)]
    (codeMat 335) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane472GenSource0074 :
    QuotientRankAtLeast (spanCodes [290, 130, 70, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 12, 2, 1] [(290, 12), (130, 3), (70, 483), (18, 2), (10, 386)]
    (codeMat 94) (codeMat 99) (codeMat 172) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit128_lb15_wc

theorem plane472GenSource0075 :
    QuotientRankAtLeast (spanCodes [289, 133, 65, 21, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(289, 20), (133, 235), (65, 130), (21, 232), (9, 128), (3, 8)]
    (codeMat 206) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane472GenSource0076 :
    QuotientRankAtLeast (spanCodes [290, 132, 66, 22, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(290, 136), (132, 232), (66, 30), (22, 224), (10, 28), (1, 3)]
    (codeMat 183) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane472GenSource0077 :
    QuotientRankAtLeast (spanCodes [288, 149, 84, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(288, 32), (149, 10), (84, 500), (8, 384), (2, 1)]
    (codeMat 177) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane472GenSource0078 :
    QuotientRankAtLeast (spanCodes [275, 145, 80, 49, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(275, 474), (145, 378), (80, 170), (49, 78), (10, 367), (4, 288)]
    (codeMat 355) (codeMat 345) (codeMat 345) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit76_lb15_unconditional

theorem plane472GenSource0079 :
    QuotientRankAtLeast (spanCodes [273, 146, 80, 51, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(273, 123), (146, 27), (80, 363), (51, 97), (10, 430), (4, 16)]
    (codeMat 334) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

end QiushiMatmul
