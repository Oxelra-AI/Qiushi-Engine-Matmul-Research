import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit149From65
import QiushiOrbit29FP
import QiushiOrbit35FP
import QiushiStep128Mono189From80T
import QiushiStep128Mono190From72
import QiushiWcOrbit197Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0250 :
    QuotientRankAtLeast (spanCodes [260, 163, 68, 16, 11]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 68, 16, 10, 1] [(260, 27), (163, 340), (68, 350), (16, 256), (11, 272)]
    (codeMat 158) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit149_lb15_mono

theorem plane491GenSource0251 :
    QuotientRankAtLeast (spanCodes [272, 146, 80, 49, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 128, 32, 10, 1] [(272, 356), (146, 32), (80, 484), (49, 366), (4, 1)]
    (codeMat 313) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit190_lb15_mono

theorem plane491GenSource0252 :
    QuotientRankAtLeast (spanCodes [274, 144, 80, 51, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(274, 356), (144, 32), (80, 480), (51, 367), (4, 1)]
    (codeMat 305) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane491GenSource0253 :
    QuotientRankAtLeast (spanCodes [257, 128, 83, 35, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 128, 32, 10, 1] [(257, 452), (128, 1), (83, 463), (35, 160), (7, 128)]
    (codeMat 92) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit190_lb15_mono

theorem plane491GenSource0254 :
    QuotientRankAtLeast (spanCodes [257, 128, 80, 33, 4, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 20), (128, 8), (80, 104), (33, 148), (4, 2), (2, 1)]
    (codeMat 417) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0255 :
    QuotientRankAtLeast (spanCodes [256, 129, 80, 33, 4, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 3), (129, 139), (80, 252), (33, 148), (4, 2), (3, 130)]
    (codeMat 141) (codeMat 94) (codeMat 500) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0256 :
    QuotientRankAtLeast (spanCodes [264, 137, 81, 41, 5, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(264, 224), (137, 151), (81, 148), (41, 104), (5, 8), (3, 1)]
    (codeMat 185) (codeMat 474) (codeMat 395) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0257 :
    QuotientRankAtLeast (spanCodes [256, 128, 80, 33, 4, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(256, 2), (128, 1), (80, 68), (33, 160), (4, 16), (2, 8)]
    (codeMat 140) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane491GenSource0258 :
    QuotientRankAtLeast (spanCodes [257, 129, 80, 32, 4, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 20), (129, 28), (80, 224), (32, 128), (4, 2), (2, 3)]
    (codeMat 161) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0259 :
    QuotientRankAtLeast (spanCodes [276, 144, 84, 50, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(276, 316), (144, 438), (84, 317), (50, 170), (1, 128)]
    (codeMat 460) (codeMat 470) (codeMat 213) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

end QiushiMatmul
