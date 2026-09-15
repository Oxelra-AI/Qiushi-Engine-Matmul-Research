import QiushiPlane427GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiOrbit35FP
import QiushiStep128Mono158From72
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit187Dispatch
import QiushiWcOrbit220Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane427GenSource0060 :
    QuotientRankAtLeast (spanCodes [320, 206, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(320, 192), (206, 442), (36, 1), (16, 36), (1, 16)]
    (codeMat 267) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane427GenSource0061 :
    QuotientRankAtLeast (spanCodes [334, 192, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(334, 426), (192, 192), (36, 36), (16, 1), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane427GenSource0062 :
    QuotientRankAtLeast (spanCodes [384, 36, 16, 14, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [192, 32, 20, 10, 1] [(384, 192), (36, 63), (16, 32), (14, 11), (1, 1)]
    (codeMat 273) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit158_lb15_mono

theorem plane427GenSource0063 :
    QuotientRankAtLeast (spanCodes [394, 32, 16, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(394, 140), (32, 1), (16, 3), (4, 8), (1, 32)]
    (codeMat 330) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane427GenSource0064 :
    QuotientRankAtLeast (spanCodes [258, 136, 32, 16, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 20), (136, 96), (32, 1), (16, 8), (4, 2), (1, 128)]
    (codeMat 266) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane427GenSource0065 :
    QuotientRankAtLeast (spanCodes [396, 36, 16, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(396, 172), (36, 3), (16, 9), (2, 8), (1, 32)]
    (codeMat 331) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane427GenSource0066 :
    QuotientRankAtLeast (spanCodes [264, 132, 36, 16, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(264, 224), (132, 20), (36, 8), (16, 3), (2, 2), (1, 128)]
    (codeMat 267) (codeMat 98) (codeMat 140) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane427GenSource0067 :
    QuotientRankAtLeast (spanCodes [398, 78, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(398, 43), (78, 11), (36, 511), (16, 384), (1, 1)]
    (codeMat 305) (codeMat 421) (codeMat 179) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane427GenSource0068 :
    QuotientRankAtLeast (spanCodes [324, 134, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(324, 422), (134, 138), (36, 128), (16, 1), (1, 390)]
    (codeMat 234) (codeMat 106) (codeMat 396) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane427GenSource0069 :
    QuotientRankAtLeast (spanCodes [384, 66, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(384, 32), (66, 10), (36, 390), (16, 128), (1, 1)]
    (codeMat 161) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

end QiushiMatmul
