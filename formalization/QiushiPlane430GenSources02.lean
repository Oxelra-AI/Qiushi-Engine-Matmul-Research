import QiushiPlane430GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiOrbit29FP
import QiushiStep128Mono346From214T
import QiushiWcOrbit141Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane430GenSource0020 :
    QuotientRankAtLeast (spanCodes [424, 100, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [424, 100, 16, 1] [(424, 424), (100, 100), (16, 16), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit346_lb16_mono

theorem plane430GenSource0021 :
    QuotientRankAtLeast (spanCodes [426, 100, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [424, 100, 16, 1] [(426, 477), (100, 100), (16, 16), (1, 1)]
    (codeMat 465) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit346_lb16_mono

theorem plane430GenSource0022 :
    QuotientRankAtLeast (spanCodes [428, 100, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [424, 100, 16, 1] [(428, 477), (100, 101), (16, 16), (1, 1)]
    (codeMat 401) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit346_lb16_mono

theorem plane430GenSource0023 :
    QuotientRankAtLeast (spanCodes [430, 100, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [424, 100, 16, 1] [(430, 424), (100, 101), (16, 16), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit346_lb16_mono

theorem plane430GenSource0024 :
    QuotientRankAtLeast (spanCodes [66, 32, 16, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(66, 133), (32, 32), (16, 40), (6, 1), (1, 2)]
    (codeMat 273) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane430GenSource0025 :
    QuotientRankAtLeast (spanCodes [130, 100, 16, 8, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(130, 32), (100, 135), (16, 8), (8, 1), (1, 3)]
    (codeMat 346) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane430GenSource0026 :
    QuotientRankAtLeast (spanCodes [130, 100, 16, 14, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(130, 2), (100, 349), (16, 1), (14, 296), (1, 32)]
    (codeMat 106) (codeMat 302) (codeMat 302) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

theorem plane430GenSource0027 :
    QuotientRankAtLeast (spanCodes [128, 100, 16, 14, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(128, 2), (100, 381), (16, 1), (14, 296), (1, 32)]
    (codeMat 98) (codeMat 302) (codeMat 302) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

theorem plane430GenSource0028 :
    QuotientRankAtLeast (spanCodes [132, 100, 16, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(132, 160), (100, 228), (16, 2), (8, 3), (2, 16), (1, 24)]
    (codeMat 266) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane430GenSource0029 :
    QuotientRankAtLeast (spanCodes [164, 100, 16, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(164, 132), (100, 164), (16, 3), (2, 1), (1, 9)]
    (codeMat 281) (codeMat 267) (codeMat 282) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

end QiushiMatmul
