import QiushiPlane453GenData
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiStep81Qdim2Generated
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane453GenSource0140 :
    QuotientRankAtLeast (spanCodes [257, 131, 66, 35, 18, 10, 6]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(257, 502), (131, 100), (66, 329), (35, 240), (18, 32), (10, 328), (6, 128)]
    (codeMat 94) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane453GenSource0141 :
    QuotientRankAtLeast (spanCodes [258, 128, 65, 32, 17, 10, 5]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 429), (128, 219), (65, 63), (32, 360), (17, 280), (10, 312), (5, 128)]
    (codeMat 94) (codeMat 351) (codeMat 239) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane453GenSource0142 :
    QuotientRankAtLeast (spanCodes [259, 129, 64, 33, 16, 10, 4]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(259, 274), (129, 429), (64, 219), (33, 80), (16, 360), (10, 408), (4, 128)]
    (codeMat 94) (codeMat 171) (codeMat 485) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane453GenSource0143 :
    QuotientRankAtLeast (spanCodes [262, 134, 68, 38, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(262, 502), (134, 457), (68, 402), (38, 112), (20, 456), (10, 208), (1, 128)]
    (codeMat 95) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane453GenSource0144 :
    QuotientRankAtLeast (spanCodes [262, 130, 68, 34, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(262, 374), (130, 219), (68, 402), (34, 240), (20, 408), (10, 208), (1, 128)]
    (codeMat 86) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane453GenSource0145 :
    QuotientRankAtLeast (spanCodes [262, 128, 68, 32, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(262, 228), (128, 219), (68, 402), (32, 32), (20, 280), (10, 208), (1, 128)]
    (codeMat 87) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane453GenSource0146 :
    QuotientRankAtLeast (spanCodes [128, 65, 32, 17, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(128, 128), (65, 216), (32, 54), (17, 10), (9, 3), (5, 40), (3, 8)]
    (codeMat 267) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane453GenSource0147 :
    QuotientRankAtLeast (spanCodes [288, 161, 65, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(288, 511), (161, 380), (65, 1), (17, 96), (8, 8), (5, 384), (2, 256)]
    (codeMat 85) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane453GenSource0148 :
    QuotientRankAtLeast (spanCodes [288, 161, 64, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(288, 130), (161, 253), (64, 9), (16, 360), (9, 8), (4, 128), (3, 256)]
    (codeMat 95) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane453GenSource0149 :
    QuotientRankAtLeast (spanCodes [289, 160, 65, 17, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(289, 127), (160, 287), (65, 8), (17, 131), (9, 1), (5, 384), (3, 128)]
    (codeMat 107) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
