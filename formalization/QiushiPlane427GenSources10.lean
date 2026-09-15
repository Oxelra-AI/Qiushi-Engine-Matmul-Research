import QiushiPlane427GenData
import QiushiCertifiedTransport
import QiushiOrbit31FP
import QiushiStep99Orbit55Dispatch
import QiushiWcOrbit143Dispatch
import QiushiWcOrbit157Dispatch
import QiushiWcOrbit187Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane427GenSource0100 :
    QuotientRankAtLeast (spanCodes [388, 74, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(388, 294), (74, 10), (36, 390), (16, 128), (1, 1)]
    (codeMat 177) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane427GenSource0101 :
    QuotientRankAtLeast (spanCodes [448, 36, 16, 14, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 20, 10, 1] [(448, 128), (36, 63), (16, 1), (14, 52), (1, 32)]
    (codeMat 266) (codeMat 358) (codeMat 158) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit157_lb15_wc

theorem plane427GenSource0102 :
    QuotientRankAtLeast (spanCodes [450, 34, 16, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(450, 80), (34, 22), (16, 2), (10, 21), (6, 32), (1, 40)]
    (codeMat 266) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane427GenSource0103 :
    QuotientRankAtLeast (spanCodes [134, 64, 36, 16, 14, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(134, 138), (64, 1), (36, 438), (16, 32), (14, 134), (1, 2)]
    (codeMat 140) (codeMat 309) (codeMat 309) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane427GenSource0104 :
    QuotientRankAtLeast (spanCodes [130, 66, 36, 16, 14, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(130, 1), (66, 44), (36, 438), (16, 2), (14, 304), (1, 32)]
    (codeMat 85) (codeMat 302) (codeMat 302) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane427GenSource0105 :
    QuotientRankAtLeast (spanCodes [262, 70, 36, 16, 14, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(262, 170), (70, 135), (36, 32), (16, 438), (14, 132), (1, 2)]
    (codeMat 207) (codeMat 179) (codeMat 421) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane427GenSource0106 :
    QuotientRankAtLeast (spanCodes [256, 132, 36, 16, 14, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(256, 1), (132, 14), (36, 2), (16, 32), (14, 274), (1, 438)]
    (codeMat 156) (codeMat 93) (codeMat 372) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane427GenSource0107 :
    QuotientRankAtLeast (spanCodes [258, 128, 36, 16, 14, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(258, 14), (128, 1), (36, 32), (16, 2), (14, 164), (1, 438)]
    (codeMat 212) (codeMat 107) (codeMat 428) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane427GenSource0108 :
    QuotientRankAtLeast (spanCodes [258, 130, 36, 16, 14, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(258, 46), (130, 3), (36, 32), (16, 2), (14, 164), (1, 438)]
    (codeMat 215) (codeMat 107) (codeMat 428) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane427GenSource0109 :
    QuotientRankAtLeast (spanCodes [392, 72, 36, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [400, 84, 32, 2, 1] [(392, 452), (72, 3), (36, 432), (16, 32), (1, 2)]
    (codeMat 143) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit143_lb14_wc

end QiushiMatmul
