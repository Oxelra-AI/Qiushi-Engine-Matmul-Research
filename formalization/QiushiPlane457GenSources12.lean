import QiushiPlane457GenData
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiStep81Qdim2Generated
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane457GenSource0120 :
    QuotientRankAtLeast (spanCodes [257, 131, 67, 35, 16, 10, 4]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(257, 274), (131, 429), (67, 374), (35, 80), (16, 360), (10, 240), (4, 128)]
    (codeMat 94) (codeMat 234) (codeMat 461) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane457GenSource0121 :
    QuotientRankAtLeast (spanCodes [259, 131, 65, 33, 16, 10, 4]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(259, 402), (131, 429), (65, 219), (33, 80), (16, 360), (10, 408), (4, 128)]
    (codeMat 95) (codeMat 171) (codeMat 485) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane457GenSource0122 :
    QuotientRankAtLeast (spanCodes [256, 132, 69, 37, 20, 9, 3]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(256, 63), (132, 502), (69, 228), (37, 312), (20, 112), (9, 32), (3, 128)]
    (codeMat 95) (codeMat 500) (codeMat 94) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane457GenSource0123 :
    QuotientRankAtLeast (spanCodes [386, 66, 34, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(386, 71), (66, 199), (34, 55), (18, 63), (10, 31), (6, 1), (1, 3)]
    (codeMat 273) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane457GenSource0124 :
    QuotientRankAtLeast (spanCodes [320, 129, 33, 16, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(320, 128), (129, 112), (33, 20), (16, 9), (8, 54), (4, 32), (2, 8)]
    (codeMat 267) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane457GenSource0125 :
    QuotientRankAtLeast (spanCodes [320, 129, 33, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(320, 128), (129, 196), (33, 52), (17, 28), (8, 32), (5, 2), (2, 3)]
    (codeMat 273) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane457GenSource0126 :
    QuotientRankAtLeast (spanCodes [256, 160, 96, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (160, 149), (96, 148), (16, 360), (10, 96), (4, 128), (1, 256)]
    (codeMat 92) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane457GenSource0127 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 54), (128, 8), (68, 22), (20, 70), (8, 128), (2, 1), (1, 2)]
    (codeMat 161) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane457GenSource0128 :
    QuotientRankAtLeast (spanCodes [260, 164, 96, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 360), (164, 246), (96, 97), (20, 29), (8, 8), (2, 3), (1, 1)]
    (codeMat 465) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane457GenSource0129 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 32, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (132, 150), (68, 149), (32, 130), (20, 406), (10, 227), (1, 511)]
    (codeMat 412) (codeMat 233) (codeMat 233) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
