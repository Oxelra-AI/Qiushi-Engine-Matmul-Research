import QiushiPlane489GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiMonoOrbit118From31
import QiushiMonoOrbit98From31T
import QiushiOrbit31FP
import QiushiPlane270GenFinal
import QiushiWcOrbit157Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane489GenSource0130 :
    QuotientRankAtLeast (spanCodes [257, 32, 16, 9, 4, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(257, 112), (32, 1), (16, 2), (9, 54), (4, 8), (3, 32)]
    (codeMat 266) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane489GenSource0131 :
    QuotientRankAtLeast (spanCodes [258, 32, 18, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(258, 112), (32, 1), (18, 54), (10, 52), (4, 8), (1, 32)]
    (codeMat 266) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane489GenSource0132 :
    QuotientRankAtLeast (spanCodes [257, 65, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [320, 32, 2, 1] [(257, 321), (65, 1), (9, 2), (3, 32)]
    (codeMat 93) (codeMat 279) (codeMat 279) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane270Gen_lb15

theorem plane489GenSource0133 :
    QuotientRankAtLeast (spanCodes [256, 65, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [320, 32, 2, 1] [(256, 320), (65, 1), (8, 2), (2, 32)]
    (codeMat 85) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane270Gen_lb15

theorem plane489GenSource0134 :
    QuotientRankAtLeast (spanCodes [258, 64, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 20, 8, 2, 1] [(258, 136), (64, 3), (10, 148), (6, 128), (1, 2)]
    (codeMat 141) (codeMat 177) (codeMat 417) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit98_lb15_mono

theorem plane489GenSource0135 :
    QuotientRankAtLeast (spanCodes [258, 67, 34, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(258, 135), (67, 173), (34, 132), (10, 164), (4, 2)]
    (codeMat 143) (codeMat 141) (codeMat 226) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane489GenSource0136 :
    QuotientRankAtLeast (spanCodes [258, 65, 35, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 20, 10, 1] [(258, 138), (65, 1), (35, 160), (10, 148), (7, 128)]
    (codeMat 205) (codeMat 179) (codeMat 421) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit157_lb15_wc

theorem plane489GenSource0137 :
    QuotientRankAtLeast (spanCodes [258, 66, 38, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(258, 173), (66, 133), (38, 164), (10, 134), (1, 2)]
    (codeMat 207) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane489GenSource0138 :
    QuotientRankAtLeast (spanCodes [258, 65, 34, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 12, 2, 1] [(258, 166), (65, 32), (34, 139), (10, 136), (5, 2)]
    (codeMat 331) (codeMat 188) (codeMat 103) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit118_lb15_mono

theorem plane489GenSource0139 :
    QuotientRankAtLeast (spanCodes [258, 64, 34, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(258, 82), (64, 2), (34, 100), (10, 68), (4, 9), (1, 1)]
    (codeMat 161) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

end QiushiMatmul
