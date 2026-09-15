import QiushiPlane482GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiStep81Qdim2Generated
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane482GenSource0100 :
    QuotientRankAtLeast (spanCodes [258, 134, 70, 38, 18, 12, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 451), (134, 196), (70, 322), (38, 280), (18, 32), (12, 80), (1, 128)]
    (codeMat 93) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane482GenSource0101 :
    QuotientRankAtLeast (spanCodes [256, 134, 66, 34, 22, 14, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(256, 390), (134, 391), (66, 322), (34, 112), (22, 440), (14, 208), (1, 128)]
    (codeMat 93) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane482GenSource0102 :
    QuotientRankAtLeast (spanCodes [258, 132, 68, 36, 16, 14, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 69), (132, 68), (68, 450), (36, 360), (16, 32), (14, 80), (1, 128)]
    (codeMat 85) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane482GenSource0103 :
    QuotientRankAtLeast (spanCodes [262, 134, 68, 34, 16, 14, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(262, 374), (134, 429), (68, 274), (34, 240), (16, 360), (14, 80), (1, 128)]
    (codeMat 94) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane482GenSource0104 :
    QuotientRankAtLeast (spanCodes [258, 134, 68, 36, 16, 14, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 100), (134, 301), (68, 402), (36, 32), (16, 360), (14, 208), (1, 128)]
    (codeMat 94) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane482GenSource0105 :
    QuotientRankAtLeast (spanCodes [262, 132, 66, 38, 22, 12, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(262, 451), (132, 263), (66, 322), (38, 280), (22, 312), (12, 208), (1, 128)]
    (codeMat 85) (codeMat 190) (codeMat 355) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane482GenSource0106 :
    QuotientRankAtLeast (spanCodes [256, 134, 66, 34, 22, 12, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(256, 1), (134, 391), (66, 450), (34, 456), (22, 440), (12, 80), (1, 128)]
    (codeMat 84) (codeMat 158) (codeMat 358) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane482GenSource0107 :
    QuotientRankAtLeast (spanCodes [262, 132, 70, 34, 18, 12, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(262, 329), (132, 301), (70, 402), (34, 328), (18, 360), (12, 80), (1, 128)]
    (codeMat 87) (codeMat 142) (codeMat 354) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane482GenSource0108 :
    QuotientRankAtLeast (spanCodes [262, 128, 70, 32, 18, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(262, 326), (128, 3), (70, 324), (32, 432), (18, 24), (12, 160), (1, 256)]
    (codeMat 92) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane482GenSource0109 :
    QuotientRankAtLeast (spanCodes [262, 128, 66, 38, 22, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(262, 327), (128, 325), (66, 68), (38, 184), (22, 168), (14, 160), (1, 256)]
    (codeMat 85) (codeMat 486) (codeMat 157) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
