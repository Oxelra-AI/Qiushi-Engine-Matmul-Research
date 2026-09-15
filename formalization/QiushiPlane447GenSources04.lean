import QiushiPlane447GenData
import QiushiCertifiedTransport
import QiushiStep126Mono175From75
import QiushiStep128Mono346From214T
import QiushiStep128Mono348From201
import QiushiWcOrbit213Dispatch
import QiushiWcOrbit214Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane447GenSource0040 :
    QuotientRankAtLeast (spanCodes [306, 160, 108, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 228, 16, 1] [(306, 483), (160, 228), (108, 278), (1, 16)]
    (codeMat 271) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit348_lb16_mono

theorem plane447GenSource0041 :
    QuotientRankAtLeast (spanCodes [280, 138, 68, 42, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(280, 287), (138, 132), (68, 10), (42, 96), (1, 1)]
    (codeMat 169) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane447GenSource0042 :
    QuotientRankAtLeast (spanCodes [262, 148, 68, 52, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 20, 10, 1] [(262, 20), (148, 262), (68, 11), (52, 434), (1, 1)]
    (codeMat 489) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit175_lb16_mono

theorem plane447GenSource0043 :
    QuotientRankAtLeast (spanCodes [306, 160, 114, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [424, 100, 16, 1] [(306, 476), (160, 101), (114, 477), (1, 16)]
    (codeMat 396) (codeMat 188) (codeMat 103) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit346_lb16_mono

theorem plane447GenSource0044 :
    QuotientRankAtLeast (spanCodes [264, 154, 78, 58, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(264, 507), (154, 132), (78, 10), (58, 96), (1, 1)]
    (codeMat 185) (codeMat 421) (codeMat 179) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane447GenSource0045 :
    QuotientRankAtLeast (spanCodes [306, 160, 118, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 228, 16, 1] [(306, 263), (160, 228), (118, 278), (1, 16)]
    (codeMat 397) (codeMat 190) (codeMat 355) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit348_lb16_mono

theorem plane447GenSource0046 :
    QuotientRankAtLeast (spanCodes [306, 160, 120, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [424, 100, 16, 1] [(306, 101), (160, 441), (120, 440), (1, 16)]
    (codeMat 206) (codeMat 286) (codeMat 303) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit346_lb16_mono

theorem plane447GenSource0047 :
    QuotientRankAtLeast (spanCodes [306, 160, 122, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 228, 16, 1] [(306, 228), (160, 483), (122, 498), (1, 16)]
    (codeMat 207) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit348_lb16_mono

theorem plane447GenSource0048 :
    QuotientRankAtLeast (spanCodes [268, 158, 66, 62, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(268, 97), (158, 143), (66, 10), (62, 505), (1, 1)]
    (codeMat 425) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane447GenSource0049 :
    QuotientRankAtLeast (spanCodes [270, 156, 66, 60, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(270, 143), (156, 107), (66, 10), (60, 496), (1, 1)]
    (codeMat 489) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

end QiushiMatmul
