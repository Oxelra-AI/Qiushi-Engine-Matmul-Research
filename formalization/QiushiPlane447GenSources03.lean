import QiushiPlane447GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit350From150
import QiushiStep126Mono175From75
import QiushiStep128Mono343From214
import QiushiStep128Mono346From214T
import QiushiStep128Mono348From201
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit213Dispatch
import QiushiWcOrbit214Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane447GenSource0030 :
    QuotientRankAtLeast (spanCodes [296, 160, 66, 26, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(296, 506), (160, 383), (66, 11), (26, 33), (1, 1)]
    (codeMat 225) (codeMat 311) (codeMat 307) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane447GenSource0031 :
    QuotientRankAtLeast (spanCodes [306, 160, 90, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 228, 16, 1] [(306, 451), (160, 295), (90, 450), (1, 16)]
    (codeMat 206) (codeMat 190) (codeMat 355) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit350_lb16_mono

theorem plane447GenSource0032 :
    QuotientRankAtLeast (spanCodes [300, 160, 66, 30, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(300, 496), (160, 411), (66, 10), (30, 133), (1, 1)]
    (codeMat 169) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane447GenSource0033 :
    QuotientRankAtLeast (spanCodes [306, 160, 94, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [298, 100, 16, 1] [(306, 315), (160, 350), (94, 298), (1, 16)]
    (codeMat 207) (codeMat 188) (codeMat 103) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit343_lb16_mono

theorem plane447GenSource0034 :
    QuotientRankAtLeast (spanCodes [306, 160, 96, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [424, 100, 16, 1] [(306, 476), (160, 441), (96, 440), (1, 16)]
    (codeMat 204) (codeMat 314) (codeMat 271) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit346_lb16_mono

theorem plane447GenSource0035 :
    QuotientRankAtLeast (spanCodes [306, 160, 98, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 228, 16, 1] [(306, 263), (160, 483), (98, 498), (1, 16)]
    (codeMat 205) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit348_lb16_mono

theorem plane447GenSource0036 :
    QuotientRankAtLeast (spanCodes [276, 134, 66, 38, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 20, 10, 1] [(276, 160), (134, 20), (66, 11), (38, 262), (1, 1)]
    (codeMat 169) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit175_lb16_mono

theorem plane447GenSource0037 :
    QuotientRankAtLeast (spanCodes [286, 140, 74, 44, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(286, 279), (140, 143), (74, 10), (44, 505), (1, 1)]
    (codeMat 313) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane447GenSource0038 :
    QuotientRankAtLeast (spanCodes [280, 138, 66, 42, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 20, 10, 1] [(280, 160), (138, 31), (66, 11), (42, 269), (1, 1)]
    (codeMat 161) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit175_lb16_mono

theorem plane447GenSource0039 :
    QuotientRankAtLeast (spanCodes [306, 160, 106, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [424, 100, 16, 1] [(306, 441), (160, 101), (106, 477), (1, 16)]
    (codeMat 270) (codeMat 412) (codeMat 111) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit346_lb16_mono

end QiushiMatmul
