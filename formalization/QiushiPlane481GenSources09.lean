import QiushiPlane481GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit124From35T
import QiushiOrbit35FP
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit72Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane481GenSource0090 :
    QuotientRankAtLeast (spanCodes [258, 96, 16, 8, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 96), (96, 20), (16, 128), (8, 2), (4, 8), (1, 1)]
    (codeMat 273) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane481GenSource0091 :
    QuotientRankAtLeast (spanCodes [264, 138, 34, 18, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(264, 224), (138, 246), (34, 10), (18, 9), (6, 2), (1, 128)]
    (codeMat 267) (codeMat 114) (codeMat 204) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane481GenSource0092 :
    QuotientRankAtLeast (spanCodes [258, 128, 36, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(258, 100), (128, 365), (36, 1), (20, 33), (10, 21), (1, 63)]
    (codeMat 339) (codeMat 207) (codeMat 370) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane481GenSource0093 :
    QuotientRankAtLeast (spanCodes [258, 136, 32, 16, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 20), (136, 96), (32, 1), (16, 8), (4, 2), (1, 128)]
    (codeMat 266) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane481GenSource0094 :
    QuotientRankAtLeast (spanCodes [416, 104, 18, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 80, 12, 2, 1] [(416, 268), (104, 349), (18, 256), (6, 1), (1, 3)]
    (codeMat 241) (codeMat 397) (codeMat 250) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit124_lb15_mono

theorem plane481GenSource0095 :
    QuotientRankAtLeast (spanCodes [292, 132, 108, 20, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(292, 9), (132, 21), (108, 246), (20, 22), (2, 2), (1, 128)]
    (codeMat 143) (codeMat 102) (codeMat 156) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane481GenSource0096 :
    QuotientRankAtLeast (spanCodes [268, 132, 74, 34, 20, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(268, 469), (132, 97), (74, 10), (34, 352), (20, 96), (1, 16)]
    (codeMat 206) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane481GenSource0097 :
    QuotientRankAtLeast (spanCodes [268, 132, 74, 32, 20, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(268, 420), (132, 97), (74, 10), (32, 256), (20, 96), (1, 16)]
    (codeMat 142) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane481GenSource0098 :
    QuotientRankAtLeast (spanCodes [256, 128, 96, 20, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 8), (128, 1), (96, 96), (20, 20), (2, 2), (1, 128)]
    (codeMat 140) (codeMat 98) (codeMat 140) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane481GenSource0099 :
    QuotientRankAtLeast (spanCodes [268, 134, 68, 42, 20, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(268, 203), (134, 356), (68, 97), (42, 272), (20, 420), (1, 260)]
    (codeMat 85) (codeMat 485) (codeMat 171) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

end QiushiMatmul
