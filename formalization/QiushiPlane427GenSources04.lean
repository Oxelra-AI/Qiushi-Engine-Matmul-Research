import QiushiPlane427GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiOrbit35FP
import QiushiStep128Mono158From72
import QiushiWcOrbit197Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane427GenSource0040 :
    QuotientRankAtLeast (spanCodes [264, 74, 32, 16, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(264, 22), (74, 118), (32, 2), (16, 128), (4, 1), (1, 9)]
    (codeMat 273) (codeMat 141) (codeMat 226) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane427GenSource0041 :
    QuotientRankAtLeast (spanCodes [322, 36, 16, 8, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(322, 164), (36, 3), (16, 32), (8, 8), (1, 9)]
    (codeMat 275) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane427GenSource0042 :
    QuotientRankAtLeast (spanCodes [262, 68, 36, 16, 8, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(262, 255), (68, 31), (36, 9), (16, 128), (8, 2), (1, 3)]
    (codeMat 275) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane427GenSource0043 :
    QuotientRankAtLeast (spanCodes [320, 36, 16, 14, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [192, 32, 20, 10, 1] [(320, 192), (36, 63), (16, 1), (14, 52), (1, 32)]
    (codeMat 266) (codeMat 358) (codeMat 158) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit158_lb15_mono

theorem plane427GenSource0044 :
    QuotientRankAtLeast (spanCodes [326, 36, 16, 8, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(326, 173), (36, 3), (16, 32), (8, 8), (1, 9)]
    (codeMat 339) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane427GenSource0045 :
    QuotientRankAtLeast (spanCodes [258, 68, 36, 16, 8, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 224), (68, 28), (36, 8), (16, 128), (8, 2), (1, 3)]
    (codeMat 275) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane427GenSource0046 :
    QuotientRankAtLeast (spanCodes [330, 32, 16, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(330, 140), (32, 8), (16, 32), (4, 1), (1, 3)]
    (codeMat 401) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane427GenSource0047 :
    QuotientRankAtLeast (spanCodes [264, 66, 32, 16, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(264, 20), (66, 96), (32, 2), (16, 128), (4, 1), (1, 8)]
    (codeMat 273) (codeMat 140) (codeMat 98) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane427GenSource0048 :
    QuotientRankAtLeast (spanCodes [266, 136, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(266, 142), (136, 490), (36, 1), (16, 325), (1, 448)]
    (codeMat 123) (codeMat 207) (codeMat 370) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane427GenSource0049 :
    QuotientRankAtLeast (spanCodes [268, 142, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(268, 42), (142, 334), (36, 325), (16, 1), (1, 448)]
    (codeMat 122) (codeMat 335) (codeMat 426) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

end QiushiMatmul
