import QiushiGlobalOrbitUnused305Data
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiPlane274GenBindings01
import QiushiStep99Orbit68Dispatch
import QiushiStep99Orbit82Dispatch
import QiushiWcOrbit179Dispatch
import QiushiWcOrbit78Dispatch
import QiushiWcOrbit79Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane305UnusedGenSource0040 :
    QuotientRankAtLeast (spanCodes [258, 130, 84, 52, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 164, 68, 16, 10, 1] [(258, 475), (130, 27), (84, 234), (52, 164), (10, 404), (1, 288)]
    (codeMat 94) (codeMat 382) (codeMat 499) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit68_lb14_unconditional

theorem plane305UnusedGenSource0041 :
    QuotientRankAtLeast (spanCodes [258, 132, 84, 52, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(258, 10), (132, 11), (84, 244), (52, 20), (10, 274), (1, 128)]
    (codeMat 141) (codeMat 114) (codeMat 204) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane305UnusedGenSource0042 :
    QuotientRankAtLeast (spanCodes [258, 134, 84, 52, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 80, 12, 2, 1] [(258, 349), (134, 243), (84, 419), (52, 429), (10, 338), (1, 511)]
    (codeMat 230) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane274GenBound0011

theorem plane305UnusedGenSource0043 :
    QuotientRankAtLeast (spanCodes [258, 132, 84, 54, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 80, 12, 2, 1] [(258, 15), (132, 14), (84, 419), (54, 2), (10, 338), (1, 511)]
    (codeMat 477) (codeMat 123) (codeMat 236) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane274GenBound0011

theorem plane305UnusedGenSource0044 :
    QuotientRankAtLeast (spanCodes [258, 134, 84, 54, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 128, 84, 32, 10, 1] [(258, 502), (134, 127), (84, 85), (54, 128), (10, 10), (1, 1)]
    (codeMat 409) (codeMat 311) (codeMat 307) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109wc179s0Dispatch

theorem plane305UnusedGenSource0045 :
    QuotientRankAtLeast (spanCodes [258, 146, 84, 54, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 160, 96, 20, 10, 1] [(258, 450), (146, 192), (84, 213), (54, 1), (10, 96), (1, 360)]
    (codeMat 163) (codeMat 460) (codeMat 122) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit79_lb14_wc

theorem plane305UnusedGenSource0046 :
    QuotientRankAtLeast (spanCodes [258, 148, 84, 54, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [292, 160, 96, 20, 10, 1] [(258, 315), (148, 202), (84, 494), (54, 325), (10, 411), (1, 192)]
    (codeMat 311) (codeMat 370) (codeMat 207) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit82_lb14_unconditional

theorem plane305UnusedGenSource0047 :
    QuotientRankAtLeast (spanCodes [256, 160, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 256), (160, 160), (68, 68), (16, 16), (8, 8), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane305UnusedGenSource0048 :
    QuotientRankAtLeast (spanCodes [256, 164, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 256), (164, 160), (68, 68), (16, 18), (8, 9), (2, 2), (1, 1)]
    (codeMat 281) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane305UnusedGenSource0049 :
    QuotientRankAtLeast (spanCodes [258, 128, 80, 48, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 118), (128, 511), (80, 284), (48, 256), (10, 105), (4, 9), (1, 8)]
    (codeMat 185) (codeMat 190) (codeMat 355) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
