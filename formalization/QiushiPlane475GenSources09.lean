import QiushiPlane475GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiStep81Qdim2Generated
import QiushiStep99Orbit55Dispatch
import QiushiStep99Orbit56Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane475GenSource0090 :
    QuotientRankAtLeast (spanCodes [259, 128, 66, 34, 19, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(259, 91), (128, 63), (66, 502), (34, 280), (19, 440), (10, 112), (7, 128)]
    (codeMat 95) (codeMat 254) (codeMat 443) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane475GenSource0091 :
    QuotientRankAtLeast (spanCodes [257, 146, 81, 49, 10, 6]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 80, 12, 2, 1] [(257, 429), (146, 1), (81, 510), (49, 160), (10, 496), (6, 256)]
    (codeMat 95) (codeMat 334) (codeMat 442) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit56_lb14_unconditional

theorem plane475GenSource0092 :
    QuotientRankAtLeast (spanCodes [257, 131, 65, 33, 17, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(257, 391), (131, 323), (65, 390), (33, 440), (17, 408), (10, 240), (7, 128)]
    (codeMat 84) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane475GenSource0093 :
    QuotientRankAtLeast (spanCodes [261, 129, 68, 36, 21, 8, 2]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(261, 301), (129, 402), (68, 100), (36, 360), (21, 80), (8, 32), (2, 128)]
    (codeMat 87) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane475GenSource0094 :
    QuotientRankAtLeast (spanCodes [256, 135, 66, 34, 21, 10]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(256, 45), (135, 166), (66, 441), (34, 408), (21, 272), (10, 440)]
    (codeMat 214) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane475GenSource0095 :
    QuotientRankAtLeast (spanCodes [260, 128, 69, 37, 21, 9, 3]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(260, 219), (128, 63), (69, 429), (37, 408), (21, 440), (9, 360), (3, 128)]
    (codeMat 86) (codeMat 247) (codeMat 379) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane475GenSource0096 :
    QuotientRankAtLeast (spanCodes [273, 144, 81, 49, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(273, 161), (144, 3), (81, 484), (49, 160), (8, 256), (4, 8), (2, 24)]
    (codeMat 142) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane475GenSource0097 :
    QuotientRankAtLeast (spanCodes [256, 128, 65, 33, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 9), (128, 54), (65, 3), (33, 88), (9, 216), (4, 8), (3, 40)]
    (codeMat 141) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane475GenSource0098 :
    QuotientRankAtLeast (spanCodes [257, 129, 65, 33, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 11), (129, 52), (65, 2), (33, 208), (8, 128), (5, 8), (2, 32)]
    (codeMat 141) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane475GenSource0099 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 32, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 2), (130, 54), (64, 1), (32, 128), (10, 112), (6, 32), (1, 8)]
    (codeMat 140) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
