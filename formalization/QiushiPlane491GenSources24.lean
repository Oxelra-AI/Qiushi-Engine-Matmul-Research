import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep128Mono189From80T
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit220Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0240 :
    QuotientRankAtLeast (spanCodes [132, 68, 37, 16, 9, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(132, 96), (68, 224), (37, 28), (16, 9), (9, 3), (2, 8)]
    (codeMat 267) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0241 :
    QuotientRankAtLeast (spanCodes [133, 68, 37, 16, 8, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(133, 227), (68, 252), (37, 139), (16, 8), (8, 9), (3, 3)]
    (codeMat 282) (codeMat 313) (codeMat 313) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0242 :
    QuotientRankAtLeast (spanCodes [147, 80, 48, 11, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(147, 414), (80, 350), (48, 36), (11, 53), (4, 16)]
    (codeMat 331) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane491GenSource0243 :
    QuotientRankAtLeast (spanCodes [132, 76, 36, 24, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(132, 96), (76, 127), (36, 128), (24, 3), (2, 8), (1, 9)]
    (codeMat 281) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0244 :
    QuotientRankAtLeast (spanCodes [265, 160, 72, 25, 5, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(265, 245), (160, 150), (72, 130), (25, 97), (5, 9), (3, 8)]
    (codeMat 177) (codeMat 499) (codeMat 382) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0245 :
    QuotientRankAtLeast (spanCodes [264, 160, 72, 28, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(264, 129), (160, 139), (72, 128), (28, 284), (3, 32)]
    (codeMat 116) (codeMat 468) (codeMat 87) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane491GenSource0246 :
    QuotientRankAtLeast (spanCodes [258, 162, 68, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 506), (162, 170), (68, 79), (16, 16), (10, 10), (1, 1)]
    (codeMat 401) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0247 :
    QuotientRankAtLeast (spanCodes [260, 162, 68, 16, 14, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 1), (162, 69), (68, 26), (16, 320), (14, 160), (1, 16)]
    (codeMat 141) (codeMat 142) (codeMat 354) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0248 :
    QuotientRankAtLeast (spanCodes [257, 163, 64, 19, 9, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 118), (163, 157), (64, 9), (19, 104), (9, 8), (7, 128)]
    (codeMat 95) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0249 :
    QuotientRankAtLeast (spanCodes [275, 163, 83, 9, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(275, 285), (163, 171), (83, 284), (9, 32), (7, 128)]
    (codeMat 92) (codeMat 342) (codeMat 215) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

end QiushiMatmul
