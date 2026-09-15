import QiushiPlane433GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiMonoOrbit118From31
import QiushiMonoOrbit124From35T
import QiushiMonoOrbit350From150
import QiushiOrbit35FP
import QiushiStep128Mono348From201
import QiushiWcOrbit187Dispatch
import QiushiWcOrbit197Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane433GenSource0030 :
    QuotientRankAtLeast (spanCodes [258, 230, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 228, 16, 1] [(258, 262), (230, 229), (16, 16), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit348_lb16_mono

theorem plane433GenSource0031 :
    QuotientRankAtLeast (spanCodes [258, 238, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 228, 16, 1] [(258, 450), (238, 245), (16, 16), (1, 1)]
    (codeMat 273) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit350_lb16_mono

theorem plane433GenSource0032 :
    QuotientRankAtLeast (spanCodes [258, 32, 16, 14, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 12, 2, 1] [(258, 136), (32, 2), (16, 3), (14, 12), (1, 32)]
    (codeMat 330) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit118_lb15_mono

theorem plane433GenSource0033 :
    QuotientRankAtLeast (spanCodes [258, 74, 40, 16, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 96), (74, 118), (40, 2), (16, 128), (4, 8), (1, 9)]
    (codeMat 273) (codeMat 169) (codeMat 225) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane433GenSource0034 :
    QuotientRankAtLeast (spanCodes [258, 68, 36, 16, 8, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 224), (68, 28), (36, 8), (16, 128), (8, 2), (1, 3)]
    (codeMat 275) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane433GenSource0035 :
    QuotientRankAtLeast (spanCodes [258, 74, 38, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(258, 294), (74, 11), (38, 262), (16, 128), (1, 1)]
    (codeMat 185) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane433GenSource0036 :
    QuotientRankAtLeast (spanCodes [258, 140, 38, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(258, 356), (140, 334), (38, 324), (16, 1), (1, 448)]
    (codeMat 122) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane433GenSource0037 :
    QuotientRankAtLeast (spanCodes [258, 140, 32, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 80, 12, 2, 1] [(258, 80), (140, 92), (32, 2), (16, 3), (1, 256)]
    (codeMat 106) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit124_lb15_mono

theorem plane433GenSource0038 :
    QuotientRankAtLeast (spanCodes [258, 192, 16, 8, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(258, 164), (192, 2), (16, 9), (8, 8), (1, 32)]
    (codeMat 98) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane433GenSource0039 :
    QuotientRankAtLeast (spanCodes [258, 160, 96, 16, 8, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 224), (160, 28), (96, 20), (16, 3), (8, 2), (1, 128)]
    (codeMat 98) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
