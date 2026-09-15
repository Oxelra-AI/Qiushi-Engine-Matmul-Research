import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiStep81Qdim2Generated
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0290 :
    QuotientRankAtLeast (spanCodes [257, 132, 68, 36, 21, 8, 2]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(257, 69), (132, 450), (68, 68), (36, 360), (21, 80), (8, 32), (2, 128)]
    (codeMat 85) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane488GenSource0291 :
    QuotientRankAtLeast (spanCodes [261, 129, 69, 37, 20, 9, 3]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(261, 374), (129, 191), (69, 429), (37, 240), (20, 440), (9, 360), (3, 128)]
    (codeMat 87) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane488GenSource0292 :
    QuotientRankAtLeast (spanCodes [257, 130, 64, 32, 19, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(257, 69), (130, 390), (64, 1), (32, 360), (19, 112), (10, 456), (7, 128)]
    (codeMat 92) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane488GenSource0293 :
    QuotientRankAtLeast (spanCodes [259, 129, 64, 32, 19, 10, 6]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(259, 100), (129, 502), (64, 63), (32, 32), (19, 112), (10, 440), (6, 128)]
    (codeMat 86) (codeMat 473) (codeMat 409) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane488GenSource0294 :
    QuotientRankAtLeast (spanCodes [259, 130, 64, 32, 19, 10, 5]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(259, 196), (130, 1), (64, 390), (32, 32), (19, 456), (10, 112), (5, 128)]
    (codeMat 85) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane488GenSource0295 :
    QuotientRankAtLeast (spanCodes [257, 64, 32, 17, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 80), (64, 128), (32, 1), (17, 20), (8, 2), (4, 8), (2, 32)]
    (codeMat 266) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane488GenSource0296 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 32, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 34), (128, 54), (64, 9), (32, 128), (10, 112), (6, 32), (1, 8)]
    (codeMat 141) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane488GenSource0297 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 32, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 2), (130, 54), (64, 1), (32, 128), (10, 112), (6, 32), (1, 8)]
    (codeMat 140) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane488GenSource0298 :
    QuotientRankAtLeast (spanCodes [257, 129, 65, 33, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 11), (129, 52), (65, 2), (33, 208), (8, 128), (5, 8), (2, 32)]
    (codeMat 141) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane488GenSource0299 :
    QuotientRankAtLeast (spanCodes [256, 128, 65, 33, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 9), (128, 54), (65, 3), (33, 88), (9, 216), (4, 8), (3, 40)]
    (codeMat 141) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
