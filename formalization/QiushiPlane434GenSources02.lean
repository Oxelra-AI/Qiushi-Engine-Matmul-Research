import QiushiPlane434GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiMonoOrbit340From196
import QiushiMonoOrbit351From217
import QiushiOrbit35FP
import QiushiStep128Mono343From214
import QiushiStep128Mono346From214T
import QiushiStep128Mono348From201
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane434GenSource0020 :
    QuotientRankAtLeast (spanCodes [266, 224, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 100, 16, 1] [(266, 359), (224, 100), (16, 1), (1, 16)]
    (codeMat 394) (codeMat 302) (codeMat 302) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit340_lb16_mono

theorem plane434GenSource0021 :
    QuotientRankAtLeast (spanCodes [266, 230, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 228, 16, 1] [(266, 498), (230, 229), (16, 16), (1, 1)]
    (codeMat 401) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit348_lb16_mono

theorem plane434GenSource0022 :
    QuotientRankAtLeast (spanCodes [266, 232, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [298, 100, 16, 1] [(266, 298), (232, 100), (16, 1), (1, 16)]
    (codeMat 266) (codeMat 298) (codeMat 270) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit343_lb16_mono

theorem plane434GenSource0023 :
    QuotientRankAtLeast (spanCodes [266, 234, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [424, 100, 16, 1] [(266, 461), (234, 116), (16, 1), (1, 16)]
    (codeMat 458) (codeMat 270) (codeMat 298) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit346_lb16_mono

theorem plane434GenSource0024 :
    QuotientRankAtLeast (spanCodes [266, 236, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 228, 16, 1] [(266, 498), (236, 229), (16, 1), (1, 16)]
    (codeMat 330) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit348_lb16_mono

theorem plane434GenSource0025 :
    QuotientRankAtLeast (spanCodes [266, 238, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [302, 228, 16, 1] [(266, 458), (238, 245), (16, 1), (1, 16)]
    (codeMat 266) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit351_lb16_mono

theorem plane434GenSource0026 :
    QuotientRankAtLeast (spanCodes [264, 32, 16, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(264, 132), (32, 2), (16, 1), (2, 8), (1, 32)]
    (codeMat 266) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane434GenSource0027 :
    QuotientRankAtLeast (spanCodes [266, 32, 16, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(266, 140), (32, 2), (16, 3), (6, 8), (1, 32)]
    (codeMat 330) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane434GenSource0028 :
    QuotientRankAtLeast (spanCodes [264, 36, 16, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(264, 164), (36, 2), (16, 9), (2, 8), (1, 32)]
    (codeMat 267) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane434GenSource0029 :
    QuotientRankAtLeast (spanCodes [258, 68, 36, 16, 8, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 224), (68, 28), (36, 8), (16, 128), (8, 2), (1, 3)]
    (codeMat 275) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
