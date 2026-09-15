import QiushiPlane427GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiOrbit101FP
import QiushiOrbit31FP
import QiushiWcOrbit197Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane427GenSource0010 :
    QuotientRankAtLeast (spanCodes [66, 34, 16, 8, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(66, 80), (34, 22), (16, 2), (8, 1), (6, 32), (1, 8)]
    (codeMat 266) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane427GenSource0011 :
    QuotientRankAtLeast (spanCodes [70, 36, 16, 8, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84] [(70, 118), (36, 2), (16, 32), (8, 8), (1, 9)]
    (codeMat 275) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit101_lb15

theorem plane427GenSource0012 :
    QuotientRankAtLeast (spanCodes [132, 36, 16, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(132, 112), (36, 54), (16, 1), (12, 52), (2, 8), (1, 32)]
    (codeMat 266) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane427GenSource0013 :
    QuotientRankAtLeast (spanCodes [132, 36, 16, 8, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(132, 164), (36, 32), (16, 2), (8, 1), (1, 9)]
    (codeMat 282) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane427GenSource0014 :
    QuotientRankAtLeast (spanCodes [136, 32, 16, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(136, 132), (32, 1), (16, 2), (4, 8), (1, 32)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane427GenSource0015 :
    QuotientRankAtLeast (spanCodes [140, 36, 16, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84] [(140, 116), (36, 2), (16, 9), (2, 8), (1, 32)]
    (codeMat 267) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit101_lb15

theorem plane427GenSource0016 :
    QuotientRankAtLeast (spanCodes [140, 76, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(140, 458), (76, 490), (36, 448), (16, 1), (1, 325)]
    (codeMat 226) (codeMat 359) (codeMat 174) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane427GenSource0017 :
    QuotientRankAtLeast (spanCodes [132, 70, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(132, 42), (70, 11), (36, 448), (16, 325), (1, 1)]
    (codeMat 233) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane427GenSource0018 :
    QuotientRankAtLeast (spanCodes [142, 76, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(142, 458), (76, 175), (36, 448), (16, 1), (1, 325)]
    (codeMat 234) (codeMat 359) (codeMat 174) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane427GenSource0019 :
    QuotientRankAtLeast (spanCodes [196, 36, 16, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(196, 132), (36, 32), (16, 9), (2, 1), (1, 3)]
    (codeMat 281) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

end QiushiMatmul
