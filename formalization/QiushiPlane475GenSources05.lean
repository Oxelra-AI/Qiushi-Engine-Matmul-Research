import QiushiPlane475GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep128Mono189From80T
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane475GenSource0050 :
    QuotientRankAtLeast (spanCodes [128, 69, 37, 17, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(128, 128), (69, 232), (37, 30), (17, 10), (9, 3), (3, 8)]
    (codeMat 267) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane475GenSource0051 :
    QuotientRankAtLeast (spanCodes [256, 160, 96, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (160, 148), (96, 20), (10, 104), (4, 1), (1, 8)]
    (codeMat 161) (codeMat 156) (codeMat 102) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane475GenSource0052 :
    QuotientRankAtLeast (spanCodes [260, 165, 96, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(260, 32), (165, 285), (96, 278), (9, 438), (3, 1)]
    (codeMat 489) (codeMat 474) (codeMat 395) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane475GenSource0053 :
    QuotientRankAtLeast (spanCodes [258, 164, 96, 18, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 496), (164, 78), (96, 238), (18, 1), (10, 261), (1, 320)]
    (codeMat 107) (codeMat 355) (codeMat 190) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane475GenSource0054 :
    QuotientRankAtLeast (spanCodes [260, 165, 96, 21, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(260, 192), (165, 171), (96, 453), (21, 20), (9, 260), (3, 432)]
    (codeMat 215) (codeMat 339) (codeMat 467) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane475GenSource0055 :
    QuotientRankAtLeast (spanCodes [263, 165, 96, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(263, 413), (165, 444), (96, 170), (18, 1), (10, 439)]
    (codeMat 499) (codeMat 335) (codeMat 426) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane475GenSource0056 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (132, 20), (64, 1), (32, 128), (10, 96), (1, 8)]
    (codeMat 140) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane475GenSource0057 :
    QuotientRankAtLeast (spanCodes [273, 148, 81, 49, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(273, 161), (148, 69), (81, 186), (49, 160), (8, 16), (2, 320)]
    (codeMat 86) (codeMat 142) (codeMat 354) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane475GenSource0058 :
    QuotientRankAtLeast (spanCodes [256, 128, 65, 33, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (128, 128), (65, 8), (33, 28), (10, 224), (4, 3)]
    (codeMat 165) (codeMat 140) (codeMat 98) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane475GenSource0059 :
    QuotientRankAtLeast (spanCodes [273, 146, 81, 49, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(273, 95), (146, 27), (81, 287), (49, 79), (10, 507), (6, 1)]
    (codeMat 305) (codeMat 123) (codeMat 236) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
