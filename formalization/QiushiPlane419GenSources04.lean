import QiushiPlane419GenData
import QiushiCertifiedTransport
import QiushiOrbit101FP
import QiushiOrbit31FP
import QiushiStep128Mono158From72
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit114Dispatch
import QiushiWcOrbit157Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane419GenSource0040 :
    QuotientRankAtLeast (spanCodes [84, 32, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84] [(84, 84), (32, 2), (8, 1), (2, 32), (1, 8)]
    (codeMat 266) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit101_lb15

theorem plane419GenSource0041 :
    QuotientRankAtLeast (spanCodes [144, 80, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [192, 32, 20, 10, 1] [(144, 63), (80, 31), (32, 192), (10, 10), (1, 1)]
    (codeMat 281) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit158_lb15_mono

theorem plane419GenSource0042 :
    QuotientRankAtLeast (spanCodes [144, 82, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 20, 10, 1] [(144, 63), (82, 30), (32, 128), (10, 52), (1, 32)]
    (codeMat 85) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit157_lb15_wc

theorem plane419GenSource0043 :
    QuotientRankAtLeast (spanCodes [128, 80, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 20, 10, 1] [(128, 1), (80, 10), (32, 128), (10, 20), (1, 32)]
    (codeMat 84) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit157_lb15_wc

theorem plane419GenSource0044 :
    QuotientRankAtLeast (spanCodes [130, 80, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 20, 10, 1] [(130, 1), (80, 42), (32, 128), (10, 20), (1, 32)]
    (codeMat 85) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit157_lb15_wc

theorem plane419GenSource0045 :
    QuotientRankAtLeast (spanCodes [386, 32, 16, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(386, 88), (32, 2), (16, 3), (10, 28), (6, 8), (1, 32)]
    (codeMat 266) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane419GenSource0046 :
    QuotientRankAtLeast (spanCodes [276, 146, 70, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(276, 261), (146, 260), (70, 26), (32, 320), (10, 160), (1, 16)]
    (codeMat 141) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane419GenSource0047 :
    QuotientRankAtLeast (spanCodes [278, 150, 70, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(278, 437), (150, 430), (70, 10), (32, 320), (10, 176), (1, 16)]
    (codeMat 141) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane419GenSource0048 :
    QuotientRankAtLeast (spanCodes [278, 134, 68, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(278, 245), (134, 430), (68, 186), (32, 320), (10, 176), (1, 16)]
    (codeMat 143) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane419GenSource0049 :
    QuotientRankAtLeast (spanCodes [260, 130, 32, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 8, 2, 1] [(260, 1), (130, 2), (32, 8), (10, 160), (1, 256)]
    (codeMat 85) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit114_lb14_wc

end QiushiMatmul
