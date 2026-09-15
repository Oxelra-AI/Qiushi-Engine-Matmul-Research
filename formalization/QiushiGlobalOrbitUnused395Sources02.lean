import QiushiGlobalOrbitUnused395Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit10FP
import QiushiOrbit35FP
import QiushiOrbit40FP
import QiushiPlane315GenBindings00
import QiushiStep81Qdim2Generated
import QiushiWcOrbit218Dispatch
import QiushiWcOrbit75Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane395UnusedGenSource0020 :
    QuotientRankAtLeast (spanCodes [295, 131, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(295, 97), (131, 228), (96, 441), (20, 132), (10, 310)]
    (codeMat 94) (codeMat 397) (codeMat 250) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane395UnusedGenSource0021 :
    QuotientRankAtLeast (spanCodes [129, 96, 16, 8, 4, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(129, 20), (96, 96), (16, 1), (8, 8), (4, 128), (2, 2)]
    (codeMat 266) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane395UnusedGenSource0022 :
    QuotientRankAtLeast (spanCodes [128, 96, 17, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84, 128] [(128, 32), (96, 252), (17, 10), (9, 9), (5, 130), (3, 2)]
    (codeMat 267) (codeMat 313) (codeMat 313) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit40_lb12

theorem plane395UnusedGenSource0023 :
    QuotientRankAtLeast (spanCodes [258, 131, 64, 32, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 506), (131, 336), (64, 16), (32, 1), (20, 79), (10, 496)]
    (codeMat 482) (codeMat 156) (codeMat 102) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315GenBound0009

theorem plane395UnusedGenSource0024 :
    QuotientRankAtLeast (spanCodes [257, 131, 71, 39, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(257, 502), (131, 274), (71, 429), (39, 21), (20, 31), (10, 20)]
    (codeMat 275) (codeMat 492) (codeMat 115) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane395UnusedGenSource0025 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 32, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 2), (129, 68), (64, 1), (32, 16), (20, 160), (8, 8), (2, 256)]
    (codeMat 84) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane395UnusedGenSource0026 :
    QuotientRankAtLeast (spanCodes [128, 65, 33, 16, 9, 4, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 32, 20, 8, 2, 1] [(128, 288), (65, 438), (33, 30), (16, 32), (9, 54), (4, 3), (3, 2)]
    (codeMat 401) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_12

theorem plane395UnusedGenSource0027 :
    QuotientRankAtLeast (spanCodes [257, 131, 65, 33, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 148, 80, 32, 12, 2, 1] [(257, 411), (131, 235), (65, 438), (33, 155), (19, 203), (10, 81), (7, 3)]
    (codeMat 410) (codeMat 345) (codeMat 345) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o16s2Span_lb

end QiushiMatmul
