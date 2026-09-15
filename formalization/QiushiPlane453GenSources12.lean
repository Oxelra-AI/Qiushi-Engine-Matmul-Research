import QiushiPlane453GenData
import QiushiCertifiedTransport
import QiushiStep81Qdim2Generated
import QiushiStep99Orbit55Dispatch
import QiushiWcOrbit78Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane453GenSource0120 :
    QuotientRankAtLeast (spanCodes [257, 128, 68, 32, 20, 9, 3]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(257, 69), (128, 390), (68, 68), (32, 360), (20, 240), (9, 32), (3, 128)]
    (codeMat 93) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane453GenSource0121 :
    QuotientRankAtLeast (spanCodes [261, 128, 68, 37, 20, 9, 3]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(261, 263), (128, 390), (68, 196), (37, 312), (20, 112), (9, 32), (3, 128)]
    (codeMat 93) (codeMat 500) (codeMat 94) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane453GenSource0122 :
    QuotientRankAtLeast (spanCodes [256, 133, 68, 37, 20, 9, 3]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(256, 390), (133, 263), (68, 197), (37, 240), (20, 440), (9, 360), (3, 128)]
    (codeMat 85) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane453GenSource0123 :
    QuotientRankAtLeast (spanCodes [257, 129, 68, 33, 20, 8, 2]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(257, 323), (129, 322), (68, 197), (33, 408), (20, 80), (8, 360), (2, 128)]
    (codeMat 92) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane453GenSource0124 :
    QuotientRankAtLeast (spanCodes [258, 131, 64, 33, 16, 10, 4]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 402), (131, 228), (64, 219), (33, 208), (16, 32), (10, 280), (4, 128)]
    (codeMat 87) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane453GenSource0125 :
    QuotientRankAtLeast (spanCodes [258, 129, 64, 35, 16, 10, 4]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 450), (129, 197), (64, 390), (35, 80), (16, 360), (10, 240), (4, 128)]
    (codeMat 93) (codeMat 234) (codeMat 461) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane453GenSource0126 :
    QuotientRankAtLeast (spanCodes [258, 131, 65, 32, 17, 10, 5]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 196), (131, 323), (65, 390), (32, 32), (17, 408), (10, 240), (5, 128)]
    (codeMat 84) (codeMat 346) (codeMat 459) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane453GenSource0127 :
    QuotientRankAtLeast (spanCodes [257, 161, 66, 18, 10, 6]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(257, 402), (161, 159), (66, 127), (18, 1), (10, 505), (6, 365)]
    (codeMat 379) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane453GenSource0128 :
    QuotientRankAtLeast (spanCodes [289, 129, 66, 18, 10, 6]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(289, 304), (129, 15), (66, 14), (18, 45), (10, 46), (6, 438)]
    (codeMat 445) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane453GenSource0129 :
    QuotientRankAtLeast (spanCodes [256, 131, 66, 35, 18, 10, 6]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(256, 63), (131, 301), (66, 329), (35, 312), (18, 360), (10, 328), (6, 128)]
    (codeMat 86) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

end QiushiMatmul
