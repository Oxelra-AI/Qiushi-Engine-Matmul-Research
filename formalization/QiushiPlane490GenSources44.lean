import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiOrbit23FP
import QiushiStep81Qdim2Generated
import QiushiStep99Orbit55Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0440 :
    QuotientRankAtLeast (spanCodes [257, 129, 67, 35, 18, 10, 5]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(257, 91), (129, 100), (67, 329), (35, 408), (18, 32), (10, 328), (5, 128)]
    (codeMat 95) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane490GenSource0441 :
    QuotientRankAtLeast (spanCodes [256, 129, 66, 35, 19, 10, 5]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(256, 219), (129, 502), (66, 457), (35, 280), (19, 112), (10, 456), (5, 128)]
    (codeMat 94) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane490GenSource0442 :
    QuotientRankAtLeast (spanCodes [256, 193, 33, 19, 10, 5]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(256, 1), (193, 441), (33, 436), (19, 306), (10, 166), (5, 438)]
    (codeMat 156) (codeMat 206) (codeMat 498) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane490GenSource0443 :
    QuotientRankAtLeast (spanCodes [261, 129, 68, 37, 20, 8, 2]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(261, 329), (129, 274), (68, 100), (37, 328), (20, 80), (8, 32), (2, 128)]
    (codeMat 86) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane490GenSource0444 :
    QuotientRankAtLeast (spanCodes [261, 133, 68, 33, 20, 8, 2]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(261, 451), (133, 450), (68, 196), (33, 280), (20, 208), (8, 32), (2, 128)]
    (codeMat 84) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane490GenSource0445 :
    QuotientRankAtLeast (spanCodes [261, 129, 68, 37, 21, 9, 3]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(261, 451), (129, 262), (68, 196), (37, 280), (21, 112), (9, 32), (3, 128)]
    (codeMat 92) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane490GenSource0446 :
    QuotientRankAtLeast (spanCodes [261, 133, 68, 33, 21, 9, 3]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(261, 329), (133, 374), (68, 100), (33, 328), (21, 240), (9, 32), (3, 128)]
    (codeMat 95) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane490GenSource0447 :
    QuotientRankAtLeast (spanCodes [256, 32, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(256, 4), (32, 1), (16, 8), (9, 216), (4, 2), (3, 128)]
    (codeMat 266) (codeMat 92) (codeMat 116) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane490GenSource0448 :
    QuotientRankAtLeast (spanCodes [256, 32, 17, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(256, 4), (32, 1), (17, 80), (8, 8), (4, 2), (2, 128)]
    (codeMat 266) (codeMat 140) (codeMat 98) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane490GenSource0449 :
    QuotientRankAtLeast (spanCodes [256, 32, 18, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(256, 4), (32, 1), (18, 216), (10, 208), (4, 2), (1, 128)]
    (codeMat 266) (codeMat 212) (codeMat 86) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

end QiushiMatmul
