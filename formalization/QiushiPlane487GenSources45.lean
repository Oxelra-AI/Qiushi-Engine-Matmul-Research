import QiushiPlane487GenData
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiOrbit23FP
import QiushiStep81Qdim2Generated
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane487GenSource0450 :
    QuotientRankAtLeast (spanCodes [259, 128, 65, 33, 19, 10, 6]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(259, 451), (128, 1), (65, 390), (33, 408), (19, 456), (10, 112), (6, 128)]
    (codeMat 84) (codeMat 110) (codeMat 444) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane487GenSource0451 :
    QuotientRankAtLeast (spanCodes [259, 129, 65, 32, 19, 10, 6]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(259, 69), (129, 391), (65, 390), (32, 360), (19, 440), (10, 112), (6, 128)]
    (codeMat 92) (codeMat 478) (codeMat 445) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane487GenSource0452 :
    QuotientRankAtLeast (spanCodes [259, 130, 66, 32, 19, 10, 5]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(259, 197), (130, 1), (66, 391), (32, 360), (19, 456), (10, 440), (5, 128)]
    (codeMat 93) (codeMat 335) (codeMat 426) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane487GenSource0453 :
    QuotientRankAtLeast (spanCodes [258, 131, 65, 35, 16, 10, 5]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 329), (131, 429), (65, 219), (35, 456), (16, 360), (10, 408), (5, 128)]
    (codeMat 95) (codeMat 143) (codeMat 482) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane487GenSource0454 :
    QuotientRankAtLeast (spanCodes [257, 130, 67, 35, 19, 10, 4]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(257, 274), (130, 63), (67, 502), (35, 208), (19, 440), (10, 112), (4, 128)]
    (codeMat 94) (codeMat 250) (codeMat 397) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane487GenSource0455 :
    QuotientRankAtLeast (spanCodes [257, 131, 67, 34, 19, 10, 4]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(257, 402), (131, 457), (67, 502), (34, 80), (19, 456), (10, 112), (4, 128)]
    (codeMat 86) (codeMat 106) (codeMat 396) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane487GenSource0456 :
    QuotientRankAtLeast (spanCodes [259, 131, 66, 33, 18, 10, 4]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(259, 274), (131, 301), (66, 329), (33, 80), (18, 360), (10, 328), (4, 128)]
    (codeMat 86) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane487GenSource0457 :
    QuotientRankAtLeast (spanCodes [259, 129, 64, 33, 16, 10, 4]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(259, 274), (129, 429), (64, 219), (33, 80), (16, 360), (10, 408), (4, 128)]
    (codeMat 94) (codeMat 171) (codeMat 485) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane487GenSource0458 :
    QuotientRankAtLeast (spanCodes [64, 36, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(64, 4), (36, 216), (20, 208), (8, 1), (2, 128), (1, 2)]
    (codeMat 266) (codeMat 417) (codeMat 177) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane487GenSource0459 :
    QuotientRankAtLeast (spanCodes [129, 64, 33, 16, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(129, 80), (64, 128), (33, 20), (16, 1), (8, 2), (4, 32), (2, 8)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
