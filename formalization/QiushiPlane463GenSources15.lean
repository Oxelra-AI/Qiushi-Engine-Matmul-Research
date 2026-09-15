import QiushiPlane463GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit55Dispatch
import QiushiWcOrbit78Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane463GenSource0150 :
    QuotientRankAtLeast (spanCodes [273, 144, 64, 35, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(273, 171), (144, 432), (64, 192), (35, 357), (10, 96), (4, 260)]
    (codeMat 123) (codeMat 468) (codeMat 87) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane463GenSource0151 :
    QuotientRankAtLeast (spanCodes [261, 129, 68, 50, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(261, 441), (129, 118), (68, 462), (50, 495), (10, 493)]
    (codeMat 468) (codeMat 415) (codeMat 253) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane463GenSource0152 :
    QuotientRankAtLeast (spanCodes [263, 131, 68, 39, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(263, 97), (131, 170), (68, 463), (39, 96), (23, 160), (10, 464)]
    (codeMat 142) (codeMat 93) (codeMat 372) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane463GenSource0153 :
    QuotientRankAtLeast (spanCodes [304, 178, 66, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(304, 232), (178, 245), (66, 21), (10, 149), (6, 3), (1, 2)]
    (codeMat 417) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane463GenSource0154 :
    QuotientRankAtLeast (spanCodes [306, 178, 64, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(306, 246), (178, 255), (64, 1), (10, 150), (4, 128), (1, 2)]
    (codeMat 140) (codeMat 403) (codeMat 403) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane463GenSource0155 :
    QuotientRankAtLeast (spanCodes [277, 132, 68, 53, 8, 2]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(277, 106), (132, 245), (68, 269), (53, 263), (8, 1), (2, 390)]
    (codeMat 250) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane463GenSource0156 :
    QuotientRankAtLeast (spanCodes [259, 145, 65, 34, 10, 5]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(259, 168), (145, 404), (65, 45), (34, 138), (10, 139), (5, 2)]
    (codeMat 458) (codeMat 171) (codeMat 485) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane463GenSource0157 :
    QuotientRankAtLeast (spanCodes [258, 144, 65, 35, 10, 5]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(258, 170), (144, 45), (65, 438), (35, 136), (10, 408), (5, 32)]
    (codeMat 207) (codeMat 234) (codeMat 461) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane463GenSource0158 :
    QuotientRankAtLeast (spanCodes [257, 144, 66, 35, 10, 6]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(257, 274), (144, 1), (66, 137), (35, 287), (10, 139), (6, 45)]
    (codeMat 318) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane463GenSource0159 :
    QuotientRankAtLeast (spanCodes [258, 147, 64, 32, 10, 4]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(258, 135), (147, 404), (64, 45), (32, 1), (10, 139), (4, 2)]
    (codeMat 394) (codeMat 143) (codeMat 482) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

end QiushiMatmul
