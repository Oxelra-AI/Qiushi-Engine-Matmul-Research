import QiushiPlane465GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiStep81Qdim2Generated
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane465GenSource0060 :
    QuotientRankAtLeast (spanCodes [262, 132, 68, 32, 22, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(262, 100), (132, 329), (68, 402), (32, 32), (22, 328), (10, 80), (1, 128)]
    (codeMat 87) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane465GenSource0061 :
    QuotientRankAtLeast (spanCodes [257, 131, 66, 35, 18, 10, 6]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(257, 502), (131, 100), (66, 329), (35, 240), (18, 32), (10, 328), (6, 128)]
    (codeMat 94) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane465GenSource0062 :
    QuotientRankAtLeast (spanCodes [259, 130, 64, 34, 17, 10, 4]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(259, 274), (130, 219), (64, 63), (34, 80), (17, 280), (10, 312), (4, 128)]
    (codeMat 95) (codeMat 123) (codeMat 236) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane465GenSource0063 :
    QuotientRankAtLeast (spanCodes [262, 130, 68, 34, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(262, 374), (130, 219), (68, 402), (34, 240), (20, 408), (10, 208), (1, 128)]
    (codeMat 86) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane465GenSource0064 :
    QuotientRankAtLeast (spanCodes [258, 131, 66, 35, 17, 10, 6]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 129), (131, 451), (66, 263), (35, 328), (17, 280), (10, 312), (6, 128)]
    (codeMat 93) (codeMat 95) (codeMat 244) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane465GenSource0065 :
    QuotientRankAtLeast (spanCodes [257, 132, 68, 36, 21, 8, 2]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(257, 69), (132, 450), (68, 68), (36, 360), (21, 80), (8, 32), (2, 128)]
    (codeMat 85) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane465GenSource0066 :
    QuotientRankAtLeast (spanCodes [256, 145, 65, 48, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 360), (145, 502), (65, 8), (48, 3), (8, 1), (5, 256), (2, 384)]
    (codeMat 106) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane465GenSource0067 :
    QuotientRankAtLeast (spanCodes [273, 129, 65, 33, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(273, 285), (129, 502), (65, 9), (33, 104), (8, 8), (5, 256), (2, 384)]
    (codeMat 87) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane465GenSource0068 :
    QuotientRankAtLeast (spanCodes [257, 145, 65, 49, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 131), (145, 502), (65, 1), (49, 104), (8, 8), (5, 128), (2, 384)]
    (codeMat 85) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane465GenSource0069 :
    QuotientRankAtLeast (spanCodes [272, 128, 66, 32, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(272, 68), (128, 325), (66, 170), (32, 256), (10, 168), (6, 8), (1, 16)]
    (codeMat 142) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
