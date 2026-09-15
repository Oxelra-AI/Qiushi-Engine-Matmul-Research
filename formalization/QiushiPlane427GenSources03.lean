import QiushiPlane427GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiOrbit101FP
import QiushiOrbit31FP
import QiushiWcOrbit197Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane427GenSource0030 :
    QuotientRankAtLeast (spanCodes [258, 36, 16, 8, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(258, 164), (36, 2), (16, 32), (8, 8), (1, 9)]
    (codeMat 275) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane427GenSource0031 :
    QuotientRankAtLeast (spanCodes [264, 36, 16, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(264, 164), (36, 2), (16, 9), (2, 8), (1, 32)]
    (codeMat 267) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane427GenSource0032 :
    QuotientRankAtLeast (spanCodes [258, 32, 16, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(258, 80), (32, 1), (16, 2), (10, 20), (4, 8), (1, 32)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane427GenSource0033 :
    QuotientRankAtLeast (spanCodes [262, 36, 16, 8, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(262, 164), (36, 2), (16, 32), (8, 8), (1, 9)]
    (codeMat 339) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane427GenSource0034 :
    QuotientRankAtLeast (spanCodes [266, 32, 16, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84] [(266, 84), (32, 1), (16, 2), (4, 8), (1, 32)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit101_lb15

theorem plane427GenSource0035 :
    QuotientRankAtLeast (spanCodes [262, 70, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(262, 42), (70, 10), (36, 325), (16, 448), (1, 1)]
    (codeMat 161) (codeMat 407) (codeMat 405) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane427GenSource0036 :
    QuotientRankAtLeast (spanCodes [266, 74, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(266, 143), (74, 175), (36, 1), (16, 448), (1, 325)]
    (codeMat 163) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane427GenSource0037 :
    QuotientRankAtLeast (spanCodes [258, 70, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(258, 42), (70, 11), (36, 325), (16, 448), (1, 1)]
    (codeMat 169) (codeMat 407) (codeMat 405) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane427GenSource0038 :
    QuotientRankAtLeast (spanCodes [270, 74, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(270, 143), (74, 490), (36, 1), (16, 448), (1, 325)]
    (codeMat 171) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane427GenSource0039 :
    QuotientRankAtLeast (spanCodes [322, 32, 16, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(322, 132), (32, 8), (16, 32), (4, 1), (1, 3)]
    (codeMat 273) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

end QiushiMatmul
