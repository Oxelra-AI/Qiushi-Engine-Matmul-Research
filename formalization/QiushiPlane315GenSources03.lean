import QiushiPlane315GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit43From14
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiOrbit41FP
import QiushiStep81Qdim2Generated
import QiushiStep99Orbit56Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane315GenSource0030 :
    QuotientRankAtLeast (spanCodes [260, 132, 82, 36, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 80, 12, 2, 1] [(260, 3), (132, 508), (82, 336), (36, 2), (10, 160), (1, 256)]
    (codeMat 94) (codeMat 212) (codeMat 86) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit56_lb14_unconditional

theorem plane315GenSource0031 :
    QuotientRankAtLeast (spanCodes [260, 134, 70, 38, 22, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(260, 390), (134, 323), (70, 322), (38, 240), (22, 408), (10, 80), (1, 128)]
    (codeMat 92) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane315GenSource0032 :
    QuotientRankAtLeast (spanCodes [260, 130, 34, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(260, 3), (130, 2), (34, 136), (18, 128), (10, 160), (1, 432)]
    (codeMat 213) (codeMat 124) (codeMat 124) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane315GenSource0033 :
    QuotientRankAtLeast (spanCodes [260, 132, 36, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84, 384] [(260, 2), (132, 34), (36, 1), (18, 9), (10, 502), (1, 384)]
    (codeMat 299) (codeMat 86) (codeMat 212) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit41_lb12

theorem plane315GenSource0034 :
    QuotientRankAtLeast (spanCodes [258, 128, 32, 16, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 208), (128, 128), (32, 3), (16, 2), (10, 20), (6, 8), (1, 32)]
    (codeMat 266) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane315GenSource0035 :
    QuotientRankAtLeast (spanCodes [258, 160, 66, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 503), (160, 70), (66, 178), (18, 432), (10, 176), (6, 8), (1, 16)]
    (codeMat 142) (codeMat 444) (codeMat 110) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane315GenSource0036 :
    QuotientRankAtLeast (spanCodes [256, 160, 64, 18, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (160, 70), (64, 2), (18, 432), (10, 176), (4, 8), (1, 16)]
    (codeMat 140) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane315GenSource0037 :
    QuotientRankAtLeast (spanCodes [260, 160, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 432), (160, 70), (68, 176), (16, 1), (8, 2), (2, 8), (1, 16)]
    (codeMat 266) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane315GenSource0038 :
    QuotientRankAtLeast (spanCodes [256, 146, 82, 50, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (146, 511), (82, 508), (50, 488), (10, 480), (4, 128), (1, 256)]
    (codeMat 84) (codeMat 242) (codeMat 205) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane315GenSource0039 :
    QuotientRankAtLeast (spanCodes [258, 144, 82, 48, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 385), (144, 511), (82, 252), (48, 8), (10, 31), (6, 1), (1, 3)]
    (codeMat 337) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
