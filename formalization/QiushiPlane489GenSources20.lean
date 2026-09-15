import QiushiPlane489GenData
import QiushiCertifiedTransport
import QiushiOrbit29FP
import QiushiOrbit35FP
import QiushiWcOrbit187Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane489GenSource0200 :
    QuotientRankAtLeast (spanCodes [258, 129, 65, 53, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(258, 42), (129, 33), (65, 32), (53, 139), (10, 269)]
    (codeMat 492) (codeMat 486) (codeMat 157) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane489GenSource0201 :
    QuotientRankAtLeast (spanCodes [258, 132, 65, 38, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 22), (132, 20), (65, 128), (38, 31), (22, 28), (10, 224)]
    (codeMat 111) (codeMat 116) (codeMat 92) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane489GenSource0202 :
    QuotientRankAtLeast (spanCodes [258, 131, 67, 36, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 224), (131, 28), (67, 31), (36, 128), (17, 20), (10, 22)]
    (codeMat 95) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane489GenSource0203 :
    QuotientRankAtLeast (spanCodes [258, 132, 71, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(258, 68), (132, 69), (71, 71), (39, 160), (17, 168), (10, 184)]
    (codeMat 93) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane489GenSource0204 :
    QuotientRankAtLeast (spanCodes [258, 177, 65, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(258, 42), (177, 171), (65, 32), (10, 295), (5, 1)]
    (codeMat 489) (codeMat 470) (codeMat 213) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane489GenSource0205 :
    QuotientRankAtLeast (spanCodes [258, 144, 82, 50, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 246), (144, 3), (82, 252), (50, 232), (10, 224), (5, 128)]
    (codeMat 86) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane489GenSource0206 :
    QuotientRankAtLeast (spanCodes [258, 144, 67, 35, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 246), (144, 128), (67, 232), (35, 252), (10, 224), (5, 3)]
    (codeMat 183) (codeMat 172) (codeMat 99) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane489GenSource0207 :
    QuotientRankAtLeast (spanCodes [258, 131, 65, 48, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 22), (131, 28), (65, 3), (48, 128), (10, 224), (7, 8)]
    (codeMat 141) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane489GenSource0208 :
    QuotientRankAtLeast (spanCodes [258, 192, 35, 17, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 224), (192, 128), (35, 11), (17, 20), (10, 22), (7, 8)]
    (codeMat 267) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane489GenSource0209 :
    QuotientRankAtLeast (spanCodes [258, 144, 65, 39, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(258, 429), (144, 390), (65, 128), (39, 295), (10, 294)]
    (codeMat 379) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

end QiushiMatmul
