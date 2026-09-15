import QiushiGlobalOrbitUnused380Data
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiStep99Orbit67Dispatch
import QiushiWcOrbit202Dispatch
import QiushiWcOrbit241Dispatch
import QiushiWcOrbit242Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane380UnusedGenSource0020 :
    QuotientRankAtLeast (spanCodes [258, 165, 68, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 164, 68, 19, 10] [(258, 332), (165, 174), (68, 68), (19, 19), (10, 10)]
    (codeMat 345) (codeMat 279) (codeMat 279) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit242_lb16_wc

theorem plane380UnusedGenSource0021 :
    QuotientRankAtLeast (spanCodes [258, 166, 68, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 162, 68, 19, 10] [(258, 435), (166, 78), (68, 245), (19, 484), (10, 255)]
    (codeMat 190) (codeMat 443) (codeMat 254) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit241_lb16_wc

theorem plane380UnusedGenSource0022 :
    QuotientRankAtLeast (spanCodes [258, 161, 67, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 164, 68, 16, 10, 1] [(258, 269), (161, 94), (67, 175), (19, 338), (10, 191), (7, 27)]
    (codeMat 254) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit67_lb15_unconditional

theorem plane380UnusedGenSource0023 :
    QuotientRankAtLeast (spanCodes [258, 129, 68, 33, 19, 10]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 68, 8, 2, 1] [(258, 479), (129, 312), (68, 228), (33, 402), (19, 304), (10, 160)]
    (codeMat 87) (codeMat 372) (codeMat 93) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109wc202s9Dispatch

theorem plane380UnusedGenSource0024 :
    QuotientRankAtLeast (spanCodes [258, 134, 68, 38, 19, 10]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 68, 8, 2, 1] [(258, 315), (134, 476), (68, 228), (38, 306), (19, 400), (10, 160)]
    (codeMat 95) (codeMat 244) (codeMat 95) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109wc202s9Dispatch

theorem plane380UnusedGenSource0025 :
    QuotientRankAtLeast (spanCodes [256, 164, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 256), (164, 160), (68, 68), (16, 18), (8, 9), (2, 2), (1, 1)]
    (codeMat 281) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
