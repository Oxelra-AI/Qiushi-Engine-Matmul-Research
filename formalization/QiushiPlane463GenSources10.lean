import QiushiPlane463GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane463GenSource0100 :
    QuotientRankAtLeast (spanCodes [260, 151, 68, 36, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(260, 3), (151, 440), (68, 35), (36, 2), (10, 493)]
    (codeMat 286) (codeMat 141) (codeMat 226) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane463GenSource0101 :
    QuotientRankAtLeast (spanCodes [261, 150, 68, 37, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(261, 119), (150, 33), (68, 462), (37, 118), (10, 493)]
    (codeMat 190) (codeMat 207) (codeMat 370) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane463GenSource0102 :
    QuotientRankAtLeast (spanCodes [260, 148, 68, 39, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(260, 32), (148, 440), (68, 35), (39, 495), (10, 493)]
    (codeMat 351) (codeMat 169) (codeMat 225) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane463GenSource0103 :
    QuotientRankAtLeast (spanCodes [261, 149, 68, 38, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(261, 441), (149, 33), (68, 462), (38, 411), (10, 493)]
    (codeMat 183) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane463GenSource0104 :
    QuotientRankAtLeast (spanCodes [274, 130, 68, 48, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(274, 31), (130, 260), (68, 462), (48, 192), (10, 160), (1, 432)]
    (codeMat 159) (codeMat 492) (codeMat 115) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane463GenSource0105 :
    QuotientRankAtLeast (spanCodes [260, 147, 68, 32, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(260, 3), (147, 118), (68, 35), (32, 2), (10, 493)]
    (codeMat 279) (codeMat 159) (codeMat 230) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane463GenSource0106 :
    QuotientRankAtLeast (spanCodes [273, 131, 64, 48, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(273, 171), (131, 261), (64, 260), (48, 432), (10, 96), (4, 192)]
    (codeMat 93) (codeMat 230) (codeMat 159) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane463GenSource0107 :
    QuotientRankAtLeast (spanCodes [276, 130, 68, 48, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(276, 11), (130, 1), (68, 452), (48, 16), (10, 96), (1, 256)]
    (codeMat 85) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane463GenSource0108 :
    QuotientRankAtLeast (spanCodes [288, 178, 64, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(288, 8), (178, 126), (64, 128), (10, 150), (4, 1), (1, 2)]
    (codeMat 305) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane463GenSource0109 :
    QuotientRankAtLeast (spanCodes [290, 178, 66, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(290, 136), (178, 104), (66, 151), (10, 148), (6, 128), (1, 2)]
    (codeMat 143) (codeMat 177) (codeMat 417) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
