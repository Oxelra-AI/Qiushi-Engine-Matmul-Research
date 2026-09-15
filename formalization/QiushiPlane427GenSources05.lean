import QiushiPlane427GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiOrbit35FP
import QiushiStep128Mono158From72
import QiushiWcOrbit197Dispatch
import QiushiWcOrbit220Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane427GenSource0050 :
    QuotientRankAtLeast (spanCodes [326, 196, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(326, 350), (196, 399), (36, 1), (16, 16), (1, 36)]
    (codeMat 467) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane427GenSource0051 :
    QuotientRankAtLeast (spanCodes [270, 136, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(270, 143), (136, 175), (36, 1), (16, 325), (1, 448)]
    (codeMat 107) (codeMat 207) (codeMat 370) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane427GenSource0052 :
    QuotientRankAtLeast (spanCodes [324, 204, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(324, 208), (204, 426), (36, 1), (16, 36), (1, 16)]
    (codeMat 331) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane427GenSource0053 :
    QuotientRankAtLeast (spanCodes [330, 194, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(330, 442), (194, 208), (36, 36), (16, 1), (1, 16)]
    (codeMat 330) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane427GenSource0054 :
    QuotientRankAtLeast (spanCodes [322, 200, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(322, 398), (200, 193), (36, 36), (16, 1), (1, 16)]
    (codeMat 394) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane427GenSource0055 :
    QuotientRankAtLeast (spanCodes [392, 36, 16, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(392, 164), (36, 3), (16, 9), (2, 8), (1, 32)]
    (codeMat 267) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane427GenSource0056 :
    QuotientRankAtLeast (spanCodes [268, 132, 36, 16, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(268, 246), (132, 22), (36, 9), (16, 3), (2, 2), (1, 128)]
    (codeMat 267) (codeMat 102) (codeMat 156) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane427GenSource0057 :
    QuotientRankAtLeast (spanCodes [386, 36, 16, 14, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [192, 32, 20, 10, 1] [(386, 223), (36, 63), (16, 32), (14, 11), (1, 1)]
    (codeMat 465) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit158_lb15_mono

theorem plane427GenSource0058 :
    QuotientRankAtLeast (spanCodes [392, 32, 16, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(392, 132), (32, 1), (16, 3), (4, 8), (1, 32)]
    (codeMat 266) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane427GenSource0059 :
    QuotientRankAtLeast (spanCodes [258, 138, 32, 16, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 22), (138, 118), (32, 1), (16, 9), (4, 2), (1, 128)]
    (codeMat 266) (codeMat 86) (codeMat 212) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
