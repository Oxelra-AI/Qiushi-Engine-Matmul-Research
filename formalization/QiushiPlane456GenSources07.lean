import QiushiPlane456GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiOrbit101FP
import QiushiStep128Mono158From72
import QiushiStep99Orbit120Dispatch
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit157Dispatch
import QiushiWcOrbit197Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit220Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane456GenSource0070 :
    QuotientRankAtLeast (spanCodes [324, 130, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(324, 507), (130, 32), (35, 175), (20, 464), (10, 341)]
    (codeMat 351) (codeMat 377) (codeMat 369) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane456GenSource0071 :
    QuotientRankAtLeast (spanCodes [352, 161, 19, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(352, 435), (161, 143), (19, 310), (10, 402), (7, 32)]
    (codeMat 95) (codeMat 379) (codeMat 247) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane456GenSource0072 :
    QuotientRankAtLeast (spanCodes [161, 16, 8, 4, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84] [(161, 84), (16, 1), (8, 2), (4, 32), (2, 8)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit101_lb15

theorem plane456GenSource0073 :
    QuotientRankAtLeast (spanCodes [161, 17, 9, 5, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(161, 174), (17, 10), (9, 3), (5, 40), (3, 8)]
    (codeMat 267) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane456GenSource0074 :
    QuotientRankAtLeast (spanCodes [161, 16, 9, 4, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 12, 2, 1] [(161, 285), (16, 32), (9, 45), (4, 3), (3, 1)]
    (codeMat 273) (codeMat 229) (codeMat 187) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit120_lb15_unconditional

theorem plane456GenSource0075 :
    QuotientRankAtLeast (spanCodes [130, 34, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 20, 10, 1] [(130, 128), (34, 21), (20, 42), (10, 20), (1, 32)]
    (codeMat 330) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit157_lb15_wc

theorem plane456GenSource0076 :
    QuotientRankAtLeast (spanCodes [131, 34, 18, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(131, 164), (34, 10), (18, 2), (10, 34), (6, 9)]
    (codeMat 275) (codeMat 124) (codeMat 124) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane456GenSource0077 :
    QuotientRankAtLeast (spanCodes [130, 35, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [192, 32, 20, 10, 1] [(130, 192), (35, 62), (17, 11), (10, 10), (5, 32)]
    (codeMat 331) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit158_lb15_mono

theorem plane456GenSource0078 :
    QuotientRankAtLeast (spanCodes [131, 67, 34, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(131, 175), (67, 490), (34, 10), (20, 11), (10, 42)]
    (codeMat 467) (codeMat 125) (codeMat 348) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane456GenSource0079 :
    QuotientRankAtLeast (spanCodes [128, 67, 33, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(128, 16), (67, 208), (33, 399), (20, 378), (10, 209)]
    (codeMat 359) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

end QiushiMatmul
