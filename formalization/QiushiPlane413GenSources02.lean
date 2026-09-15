import QiushiPlane413GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiMonoOrbit124From35T
import QiushiMonoOrbit271From120
import QiushiStep128Mono266From98T
import QiushiStep99Orbit120Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane413GenSource0020 :
    QuotientRankAtLeast (spanCodes [200, 32, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [80, 32, 2, 1] [(200, 80), (32, 32), (2, 3), (1, 2)]
    (codeMat 273) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit266_lb15_mono

theorem plane413GenSource0021 :
    QuotientRankAtLeast (spanCodes [136, 68, 32, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 80, 12, 2, 1] [(136, 80), (68, 12), (32, 256), (2, 2), (1, 1)]
    (codeMat 161) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit124_lb15_mono

theorem plane413GenSource0022 :
    QuotientRankAtLeast (spanCodes [208, 32, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [80, 32, 2, 1] [(208, 80), (32, 32), (2, 2), (1, 3)]
    (codeMat 273) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit266_lb15_mono

theorem plane413GenSource0023 :
    QuotientRankAtLeast (spanCodes [132, 80, 32, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 80, 12, 2, 1] [(132, 12), (80, 80), (32, 256), (2, 1), (1, 2)]
    (codeMat 161) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit124_lb15_mono

theorem plane413GenSource0024 :
    QuotientRankAtLeast (spanCodes [264, 32, 24, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(264, 133), (32, 2), (24, 1), (2, 32), (1, 40)]
    (codeMat 266) (codeMat 225) (codeMat 169) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane413GenSource0025 :
    QuotientRankAtLeast (spanCodes [268, 32, 28, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 12, 2, 1] [(268, 284), (32, 32), (28, 12), (2, 2), (1, 3)]
    (codeMat 273) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit120_lb15_unconditional

theorem plane413GenSource0026 :
    QuotientRankAtLeast (spanCodes [264, 32, 28, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 12, 2, 1] [(264, 272), (32, 32), (28, 12), (2, 3), (1, 2)]
    (codeMat 273) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit120_lb15_unconditional

theorem plane413GenSource0027 :
    QuotientRankAtLeast (spanCodes [264, 32, 16, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(264, 132), (32, 2), (16, 1), (2, 8), (1, 32)]
    (codeMat 266) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane413GenSource0028 :
    QuotientRankAtLeast (spanCodes [264, 32, 20, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 12, 2, 1] [(264, 272), (32, 32), (20, 12), (2, 1), (1, 2)]
    (codeMat 273) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit120_lb15_unconditional

theorem plane413GenSource0029 :
    QuotientRankAtLeast (spanCodes [336, 32, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [336, 32, 2, 1] [(336, 336), (32, 32), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit271_lb15_mono

end QiushiMatmul
