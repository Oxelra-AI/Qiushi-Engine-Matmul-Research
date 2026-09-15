import QiushiPlane447GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit350From150
import QiushiStep126Mono175From75
import QiushiStep128Mono346From214T
import QiushiStep128Mono348From201
import QiushiStep99Orbit150Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit235Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane447GenSource0010 :
    QuotientRankAtLeast (spanCodes [296, 160, 26, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 228, 16, 1] [(296, 310), (160, 228), (26, 17), (1, 16)]
    (codeMat 267) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit350_lb16_mono

theorem plane447GenSource0011 :
    QuotientRankAtLeast (spanCodes [290, 160, 16, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(290, 333), (160, 69), (16, 1), (10, 10), (1, 16)]
    (codeMat 266) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane447GenSource0012 :
    QuotientRankAtLeast (spanCodes [290, 160, 16, 12, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(290, 20), (160, 11), (16, 1), (12, 96), (1, 256)]
    (codeMat 114) (codeMat 98) (codeMat 140) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane447GenSource0013 :
    QuotientRankAtLeast (spanCodes [290, 160, 16, 14, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(290, 31), (160, 11), (16, 1), (14, 96), (1, 256)]
    (codeMat 98) (codeMat 102) (codeMat 156) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane447GenSource0014 :
    QuotientRankAtLeast (spanCodes [282, 136, 40, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 228, 16, 1] [(282, 229), (136, 262), (40, 1), (1, 16)]
    (codeMat 394) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit348_lb16_mono

theorem plane447GenSource0015 :
    QuotientRankAtLeast (spanCodes [276, 134, 38, 14, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(276, 341), (134, 506), (38, 42), (14, 10), (1, 1)]
    (codeMat 401) (codeMat 407) (codeMat 405) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane447GenSource0016 :
    QuotientRankAtLeast (spanCodes [276, 134, 38, 12, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 20, 10, 1] [(276, 160), (134, 434), (38, 20), (12, 10), (1, 1)]
    (codeMat 465) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit175_lb16_mono

theorem plane447GenSource0017 :
    QuotientRankAtLeast (spanCodes [286, 140, 44, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [424, 100, 16, 1] [(286, 116), (140, 461), (44, 17), (1, 16)]
    (codeMat 395) (codeMat 174) (codeMat 359) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit346_lb16_mono

theorem plane447GenSource0018 :
    QuotientRankAtLeast (spanCodes [262, 138, 42, 30, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(262, 509), (138, 353), (42, 51), (30, 38), (1, 1)]
    (codeMat 409) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane447GenSource0019 :
    QuotientRankAtLeast (spanCodes [262, 142, 46, 26, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(262, 464), (142, 372), (46, 11), (26, 33), (1, 32)]
    (codeMat 267) (codeMat 486) (codeMat 157) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

end QiushiMatmul
