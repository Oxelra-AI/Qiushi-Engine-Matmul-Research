import QiushiPlane486GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiOrbit29FP
import QiushiStep81Qdim2Generated
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane486GenSource0190 :
    QuotientRankAtLeast (spanCodes [384, 67, 49, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(384, 40), (67, 175), (49, 34), (10, 166), (7, 2)]
    (codeMat 207) (codeMat 409) (codeMat 473) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane486GenSource0191 :
    QuotientRankAtLeast (spanCodes [272, 160, 66, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(272, 68), (160, 69), (66, 170), (10, 168), (6, 8), (1, 16)]
    (codeMat 142) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane486GenSource0192 :
    QuotientRankAtLeast (spanCodes [258, 130, 67, 32, 19, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 228), (130, 63), (67, 457), (32, 32), (19, 440), (10, 456), (7, 128)]
    (codeMat 87) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane486GenSource0193 :
    QuotientRankAtLeast (spanCodes [258, 128, 67, 34, 19, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 323), (128, 390), (67, 391), (34, 408), (19, 112), (10, 440), (7, 128)]
    (codeMat 85) (codeMat 253) (codeMat 415) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane486GenSource0194 :
    QuotientRankAtLeast (spanCodes [258, 128, 67, 35, 19, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 68), (128, 1), (67, 391), (35, 160), (19, 456), (10, 440), (7, 128)]
    (codeMat 92) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane486GenSource0195 :
    QuotientRankAtLeast (spanCodes [259, 129, 66, 34, 19, 10, 6]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(259, 228), (129, 502), (66, 457), (34, 160), (19, 112), (10, 456), (6, 128)]
    (codeMat 94) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane486GenSource0196 :
    QuotientRankAtLeast (spanCodes [258, 131, 65, 32, 19, 10, 5]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 301), (131, 457), (65, 63), (32, 360), (19, 456), (10, 440), (5, 128)]
    (codeMat 94) (codeMat 335) (codeMat 426) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane486GenSource0197 :
    QuotientRankAtLeast (spanCodes [258, 131, 64, 33, 19, 10, 4]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 450), (131, 391), (64, 1), (33, 80), (19, 440), (10, 456), (4, 128)]
    (codeMat 84) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane486GenSource0198 :
    QuotientRankAtLeast (spanCodes [261, 129, 68, 37, 21, 9, 3]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(261, 451), (129, 262), (68, 196), (37, 280), (21, 112), (9, 32), (3, 128)]
    (codeMat 92) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane486GenSource0199 :
    QuotientRankAtLeast (spanCodes [261, 129, 68, 37, 20, 8, 2]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(261, 329), (129, 274), (68, 100), (37, 328), (20, 80), (8, 32), (2, 128)]
    (codeMat 86) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

end QiushiMatmul
