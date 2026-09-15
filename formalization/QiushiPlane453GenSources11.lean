import QiushiPlane453GenData
import QiushiCertifiedTransport
import QiushiStep81Qdim2Generated
import QiushiStep99Orbit55Dispatch
import QiushiStep99Orbit56Dispatch
import QiushiWcOrbit119Dispatch
import QiushiWcOrbit187Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane453GenSource0110 :
    QuotientRankAtLeast (spanCodes [416, 66, 18, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(416, 138), (66, 294), (18, 128), (10, 262), (6, 1)]
    (codeMat 241) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane453GenSource0111 :
    QuotientRankAtLeast (spanCodes [417, 66, 18, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(417, 396), (66, 294), (18, 390), (10, 262), (6, 1)]
    (codeMat 177) (codeMat 500) (codeMat 94) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane453GenSource0112 :
    QuotientRankAtLeast (spanCodes [65, 17, 8, 5, 2]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 32, 12, 2, 1] [(65, 256), (17, 12), (8, 32), (5, 2), (2, 1)]
    (codeMat 337) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit119_lb14_wc

theorem plane453GenSource0113 :
    QuotientRankAtLeast (spanCodes [290, 162, 64, 16, 10, 4]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(290, 274), (162, 272), (64, 3), (16, 32), (10, 316), (4, 438)]
    (codeMat 468) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane453GenSource0114 :
    QuotientRankAtLeast (spanCodes [291, 162, 67, 19, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 80, 12, 2, 1] [(291, 510), (162, 257), (67, 429), (19, 243), (10, 430), (7, 511)]
    (codeMat 351) (codeMat 143) (codeMat 482) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit56_lb14_unconditional

theorem plane453GenSource0115 :
    QuotientRankAtLeast (spanCodes [288, 162, 64, 16, 10, 4]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(288, 2), (162, 44), (64, 438), (16, 32), (10, 316), (4, 3)]
    (codeMat 183) (codeMat 93) (codeMat 372) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane453GenSource0116 :
    QuotientRankAtLeast (spanCodes [258, 130, 68, 32, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 228), (130, 219), (68, 274), (32, 32), (20, 280), (10, 208), (1, 128)]
    (codeMat 86) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane453GenSource0117 :
    QuotientRankAtLeast (spanCodes [258, 128, 68, 34, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 374), (128, 219), (68, 274), (34, 240), (20, 408), (10, 208), (1, 128)]
    (codeMat 87) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane453GenSource0118 :
    QuotientRankAtLeast (spanCodes [258, 134, 68, 36, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 100), (134, 329), (68, 274), (36, 32), (20, 328), (10, 208), (1, 128)]
    (codeMat 95) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane453GenSource0119 :
    QuotientRankAtLeast (spanCodes [258, 132, 68, 38, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 502), (132, 457), (68, 274), (38, 112), (20, 456), (10, 208), (1, 128)]
    (codeMat 94) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

end QiushiMatmul
