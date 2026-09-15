import QiushiGlobalOrbitUnused407Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit10FP
import QiushiPlane274GenBindings01
import QiushiWcOrbit78Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane407UnusedGenSource0020 :
    QuotientRankAtLeast (spanCodes [257, 146, 83, 49, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 80, 12, 2, 1] [(257, 83), (146, 256), (83, 336), (49, 510), (10, 496), (7, 1)]
    (codeMat 489) (codeMat 236) (codeMat 123) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane274GenBound0011

theorem plane407UnusedGenSource0021 :
    QuotientRankAtLeast (spanCodes [257, 135, 66, 36, 22, 10]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(257, 263), (135, 255), (66, 31), (36, 390), (22, 245), (10, 30)]
    (codeMat 318) (codeMat 279) (codeMat 279) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane407UnusedGenSource0022 :
    QuotientRankAtLeast (spanCodes [257, 134, 67, 37, 23, 10]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 80, 12, 2, 1] [(257, 83), (134, 350), (67, 497), (37, 80), (23, 160), (10, 496)]
    (codeMat 159) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane274GenBound0011

theorem plane407UnusedGenSource0023 :
    QuotientRankAtLeast (spanCodes [256, 160, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 256), (160, 160), (68, 68), (16, 16), (8, 8), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane407UnusedGenSource0024 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 36, 16, 8, 2, 1]) 6 := by
  apply quotientRankAtLeast_weaken (n := 6) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 64, 16, 8, 4, 2, 1] [(256, 256), (132, 164), (68, 160), (36, 64), (16, 27), (8, 24), (2, 18), (1, 16)]
    (codeMat 267) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_2

end QiushiMatmul
