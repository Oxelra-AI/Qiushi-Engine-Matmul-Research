import QiushiGlobalOrbitUnused388Data
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiPlane315GenBindings00
import QiushiStep99Orbit82Dispatch
import QiushiWcOrbit213Dispatch
import QiushiWcOrbit75Dispatch
import QiushiWcOrbit78Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane388UnusedGenSource0020 :
    QuotientRankAtLeast (spanCodes [295, 164, 68, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(295, 496), (164, 373), (68, 132), (20, 411), (10, 228)]
    (codeMat 125) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane388UnusedGenSource0021 :
    QuotientRankAtLeast (spanCodes [258, 164, 68, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(258, 441), (164, 238), (68, 78), (20, 90), (10, 11), (1, 1)]
    (codeMat 401) (codeMat 307) (codeMat 311) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane388UnusedGenSource0022 :
    QuotientRankAtLeast (spanCodes [257, 160, 64, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(257, 69), (160, 170), (64, 260), (16, 16), (10, 160), (4, 320)]
    (codeMat 85) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315GenBound0009

theorem plane388UnusedGenSource0023 :
    QuotientRankAtLeast (spanCodes [259, 161, 65, 17, 10, 5]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(259, 138), (161, 397), (65, 390), (17, 402), (10, 274), (5, 365)]
    (codeMat 230) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane388UnusedGenSource0024 :
    QuotientRankAtLeast (spanCodes [259, 163, 67, 19, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [292, 160, 96, 20, 10, 1] [(259, 193), (163, 334), (67, 388), (19, 304), (10, 160), (7, 192)]
    (codeMat 93) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit82_lb14_unconditional

theorem plane388UnusedGenSource0025 :
    QuotientRankAtLeast (spanCodes [258, 135, 68, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(258, 329), (135, 269), (68, 268), (35, 434), (20, 274), (10, 20)]
    (codeMat 93) (codeMat 318) (codeMat 299) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane388UnusedGenSource0026 :
    QuotientRankAtLeast (spanCodes [258, 131, 68, 39, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(258, 349), (131, 422), (68, 268), (39, 21), (20, 30), (10, 20)]
    (codeMat 395) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane388UnusedGenSource0027 :
    QuotientRankAtLeast (spanCodes [128, 68, 36, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(128, 54), (68, 78), (36, 216), (20, 90), (8, 2), (2, 9), (1, 1)]
    (codeMat 401) (codeMat 307) (codeMat 311) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
